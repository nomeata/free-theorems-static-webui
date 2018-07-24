{-# LANGUAGE FlexibleContexts #-}


-- | Defines a function to parse a string into a list of declarations.
--   This module is based on the \'haskell-src\' package most probably included
--   with every Haskell compiler.

module Language.Haskell.FreeTheorems.Parser.Haskell98 (parse) where



import Control.Monad (foldM, liftM, liftM2)
import Control.Monad.Error (throwError)
import Control.Monad.Writer (Writer, tell)
import Data.Generics (everywhere, mkT)
import Data.List (nub)
import Language.Haskell.Parser (parseModule, ParseResult(..))
import Language.Haskell.Syntax
import Text.PrettyPrint

import qualified Language.Haskell.FreeTheorems.Syntax as S
import Language.Haskell.FreeTheorems.Frontend.Error




------- Main parser function --------------------------------------------------


-- | Parses a string to a list of declarations.
--   The string should contain a Haskell module.
--
--   This function is based on the Haskell98 parser of the \'haskell-src\'
--   package, i.e. the module \'Language.Haskell.Parser\'.
--   That parser supports only Haskell98 and a few extensions. Especially, it
--   does not support explicit quantification of type variables and thus no 
--   higher-rank functions.
--
--   The declarations returned by 'parse' include only @type@, @data@, 
--   @newtype@, @class@ and type signature declarations.
--   All other declarations and syntactical elements in the input are ignored.
--   
--   Furthermore, the following restrictions apply:
--
--   * Multi-parameter type classes are not allowed and therefore ignored. When
--     declaring a type class, the argument to the type class name must be a
--     single type variable.
--
--   * A type variable must not be applied to any type. That means, for
--     example, that the type @m a@ is not accepted.
--
--   * Contexts and @deriving@ parts in @data@ and @newtype@ declarations
--     are ignored.
--
--   * The module names are ignored. If any identifier was given qualified, the
--     module part of a qualified name is ignored.
--   
--   * Special Haskell constructors (unit, list function) are not allowed as
--     identifiers.
--
--   If a parser error occurs, as suitable error message is returned in the
--   second component of the returned tuple and the first component will be the
--   empty list.
--   However, if parsing was successful, but the parsed structures could not
--   be completely transformed into @Declaration@s, suitable transformation
--   error messages are returned in the second component while the first
--   components contains all declarations which could be transformed
--   successfully.

parse :: String -> Parsed [S.Declaration]
parse text = case parseModule text of
  ParseOk hsModule -> let decls = transform . filterDeclarations $ hsModule
                       in foldM collectDeclarations [] decls
  ParseFailed l _  -> do tell [pp ("Parse error at (" ++ show (srcLine l)
                                   ++ ":" ++ show (srcColumn l) ++ ").")]
                         return []
  where
    collectDeclarations :: [S.Declaration] -> HsDecl -> Parsed [S.Declaration]
    collectDeclarations ds d = 
      case mkDeclaration d of
        Left e   -> tell [e] >> return ds
        Right d' -> return (ds ++ [d'])
      




------- Filter declarations ---------------------------------------------------



-- | Filters all declarations of a Haskell module.

filterDeclarations :: HsModule -> [HsDecl]
filterDeclarations (HsModule _ _ _ _ ds) = filter isAcceptedDeclaration ds
  where
    isAcceptedDeclaration decl = case decl of
      HsTypeDecl _ _ _ _        -> True
      HsDataDecl _ _ _ _ _ _    -> True
      HsNewTypeDecl _ _ _ _ _ _ -> True
      HsClassDecl _ _ _ _ _     -> True
      HsTypeSig _ _ _           -> True
      otherwise                 -> False



-- | Transforms a list of declarations by simplifying type signatures.

transform :: [HsDecl] -> [HsDecl]
transform = everywhere (mkT extendTypeSignature)
  where
    -- Type signatures can be given for several names at once.
    -- This function transforms declarations such that every type signature is
    -- given for exactly one name only.
    extendTypeSignature :: [HsDecl] -> [HsDecl]
    extendTypeSignature ds = case ds of
      ((HsTypeSig l ns t):ds') -> (map (\n -> HsTypeSig l [n] t) ns) ++ ds'
      otherwise                -> ds





------- Transform declarations ------------------------------------------------



-- | Transforms a declaration.

mkDeclaration :: HsDecl -> ErrorOr S.Declaration
mkDeclaration decl = case decl of
  HsTypeDecl l n vs t               -> addErr l n (mkType n vs t)
  HsDataDecl l _ n vs cs _          -> addErr l n (mkData n vs cs)
  HsNewTypeDecl l _ n vs c _        -> addErr l n (mkNewtype n vs c)
  HsClassDecl l scs n [v] ds        -> addErr l n (mkClass scs n v ds)
  HsTypeSig l [n] (HsQualType cx t) -> addErr l n (mkSignature cx n t)

  HsClassDecl l _ n [] _      -> addErr l n (throwError missingVar)
  HsClassDecl l _ n (_:_:_) _ -> addErr l n (throwError noMultiParam)

  -- no other case con occur, see above function 'filterDeclarations'. 


missingVar   = pp "Missing type variable to be constrained by type class."
noMultiParam = pp "Multi-parameter type classes are not allowed."



-- | Adds an error message based on the name of a declaration if the given
--   transformation caused an error.

addErr :: SrcLoc -> HsName -> ErrorOr S.Declaration-> ErrorOr S.Declaration
addErr loc name e = case getError e of
  Nothing  -> e
  Just doc -> throwError $
                pp ("In the declaration of `" ++ hsNameToString name 
                    ++ "' at (" ++ show (srcLine loc) ++ ":"
                    ++ show (srcColumn loc) ++ "):")
                $$ nest 2 doc



-- | Transforms the components of a type declaration.

mkType :: HsName -> [HsName] -> HsType -> ErrorOr S.Declaration
mkType name vars ty = do
  ident <- mkIdentifier name
  tvs   <- mapM mkTypeVariable vars
  t     <- mkTypeExpression ty
  return (S.TypeDecl (S.Type ident tvs t))



-- | Transforms the components of a data declaration.

mkData :: HsName -> [HsName] -> [HsConDecl] -> ErrorOr S.Declaration
mkData name vars cons = do
  ident <- mkIdentifier name
  tvs   <- mapM mkTypeVariable vars
  ds    <- mapM mkDataConstructorDeclaration cons
  return (S.DataDecl (S.Data ident tvs ds))
       


-- | Transforms a data constructor declaration.

mkDataConstructorDeclaration :: 
    HsConDecl -> ErrorOr S.DataConstructorDeclaration

mkDataConstructorDeclaration (HsConDecl _ name btys) = mkDataConDecl name btys

mkDataConstructorDeclaration (HsRecDecl _ name rbtys) = 
  let btys = concatMap (\(l,ty) -> replicate (length l) ty) rbtys
   in mkDataConDecl name btys
  


-- | Transforms the components of a data constructor declaration.

mkDataConDecl ::
    HsName -> [HsBangType] -> ErrorOr S.DataConstructorDeclaration

mkDataConDecl name btys = do
  ident <- mkIdentifier name
  bts   <- mapM mkBangTyEx btys
  return (S.DataCon ident bts)
  where
    mkBangTyEx (HsBangedTy ty)   = liftM S.Banged   (mkTypeExpression ty)
    mkBangTyEx (HsUnBangedTy ty) = liftM S.Unbanged (mkTypeExpression ty)



-- | Transforms the components of a newtype declaration.

mkNewtype :: HsName -> [HsName] -> HsConDecl -> ErrorOr S.Declaration
mkNewtype name vars con = do
  ident   <- mkIdentifier name
  tvs     <- mapM mkTypeVariable vars
  (con,t) <- mkNewtypeConDecl con
  return (S.NewtypeDecl (S.Newtype ident tvs con t))
  where
    mkNewtypeConDecl (HsConDecl _ c bts) = mkNCD c bts
    mkNewtypeConDecl (HsRecDecl _ c bts) = mkNCD c (snd $ unzip bts)

    mkNCD c [bty] = liftM2 (,) (mkIdentifier c) (bang bty)
    mkNCD c []      = throwError errNewtype
    mkNCD c (_:_:_) = throwError errNewtype

    errNewtype = 
      pp "A `newtype' declaration must have exactly one type expression."

    bang (HsUnBangedTy ty) = mkTypeExpression ty
    bang (HsBangedTy ty)   = 
      throwError (pp "A `newtype' declaration must not use a strictness flag.")



-- | Transforms the components of a Haskell class declaration.
--   Every declaration in the class body is ignored except of type signatures.

mkClass :: HsContext -> HsName -> HsName -> [HsDecl] -> ErrorOr S.Declaration
mkClass ctx name var decls = do
  ident   <- mkIdentifier name
  tv      <- mkTypeVariable var
  superCs <- mkContext ctx >>= check tv
  sigs    <- liftM (map toSig) (mapM mkDeclaration (filter isSig decls))
    -- mapping 'isSig' is safe because after applying 'filter' no other
    -- declarations are left except of type signatures

  return (S.ClassDecl (S.Class superCs ident tv sigs))
  where
    -- Returns 'True' if a declaration is a type signature, otherwise 'False'.
    isSig :: HsDecl -> Bool
    isSig decl = case decl of
      HsTypeSig _ _ _ -> True
      otherwise       -> False

    -- Extracts a signature from a declaration.
    -- Note that no other has to be given here because all declarations passed
    -- as argument to this function are definitely type signatures.
    -- See application of 'isSig' above.
    toSig :: S.Declaration -> S.Signature
    toSig (S.TypeSig s) = s

    -- Checks if only the given type variable occurs in the second parameter.
    -- If not, an error is returned, otherwise, the list of type classes is
    -- extracted.
    check :: 
        S.TypeVariable 
        -> [(S.TypeClass, S.TypeVariable)] 
        -> ErrorOr [S.TypeClass]
    check tv@(S.TV (S.Ident v)) ctx =
      let (tcs, tvs) = unzip ctx
       in if null (filter (/= tv) tvs)
        then return tcs
        else throwError (errClass v)

    errClass v = 
      pp $ "Only `" ++ v ++ "' can be constrained by the superclasses."



-- | Transforms the components of a Haskell type signature.
--   The context is added to the type expression.

mkSignature :: HsContext -> HsName -> HsType -> ErrorOr S.Declaration
mkSignature ctx var ty = do
  context <- mkContext ctx
  ident   <- mkIdentifier var
  t       <- mkTypeExpression ty
  return $ S.TypeSig (S.Signature ident (merge context t))
  where
    -- Merges the context and the type expression. The context is represented
    -- as type abstractions.
    merge :: 
        [(S.TypeClass, S.TypeVariable)] 
        -> S.TypeExpression 
        -> S.TypeExpression
    merge ctx t =
      let -- All variables occurring in a context.
          vars      = (nub . snd . unzip) ctx
          -- Returns all classes associated to a type variable 'v' in 'ctx'.
          classes v = map fst (filter ((==) v . snd) ctx)
       in foldr (\v -> S.TypeAbs v (classes v)) t vars



-- | Transforms a Haskell context.
--   If the context contains not only variables, but also more complex types,
--   this function fails with an appropriate error message.

mkContext :: HsContext -> ErrorOr [(S.TypeClass, S.TypeVariable)]
mkContext = mapM trans
  where
    trans (qname, tys) = case tys of
      [HsTyVar var] -> do ident <- liftM S.TC (mkIdentifierQ qname)
                          tv    <- mkTypeVariable var
                          return $ (ident, tv)
      otherwise     -> throwError errContext

errContext =
  pp "Only a type variable may be constrained by a class in a context."





------- Transform type expressions --------------------------------------------



-- | Transforms a Haskell type.
--   Note that a type variable is not allowed to be applied to some type.

mkTypeExpression :: HsType -> ErrorOr S.TypeExpression
mkTypeExpression (HsTyVar var)     = liftM S.TypeVar (mkTypeVariable var)
mkTypeExpression (HsTyApp ty1 ty2) = mkAppTyEx ty1 [ty2]
mkTypeExpression (HsTyCon qname)   = mkTypeConstructorApp qname []

mkTypeExpression (HsTyFun ty1 ty2) = do
  t1 <- mkTypeExpression ty1
  t2 <- mkTypeExpression ty2
  return (S.TypeFun t1 t2)

mkTypeExpression (HsTyTuple tys)   = do
  ts <- mapM mkTypeExpression tys
  return (S.TypeCon (S.ConTuple (length ts)) ts)




-- | Collects applied types and transforms them into a type expression.

mkAppTyEx :: HsType -> [HsType] -> ErrorOr S.TypeExpression
mkAppTyEx ty tys = case ty of
  HsTyFun _ _   -> throwError $ pp ("A function type must not be applied to a "
                                    ++ "type.")
  HsTyTuple _   -> throwError (pp "A tuple type must not be applied to a type.")
  HsTyVar _     -> throwError (pp "A variable must not be applied to a type.")
  HsTyApp t1 t2 -> mkAppTyEx t1 (t2 : tys)
  HsTyCon qname -> mapM mkTypeExpression tys >>= mkTypeConstructorApp qname 



-- | Interprets a qualified name as a type constructor and applies it to a list
--   of type expressions.
--   The function type constructor is handled specially because it has to have
--   exactly two arguments.

mkTypeConstructorApp :: 
    HsQName 
    -> [S.TypeExpression] 
    -> ErrorOr S.TypeExpression

mkTypeConstructorApp (Special HsFunCon) [t1,t2] = return $ S.TypeFun t1 t2
mkTypeConstructorApp (Special HsFunCon) _       = throwError errorTypeConstructorApp

mkTypeConstructorApp qname              ts      = 
  liftM (\con -> S.TypeCon con ts) (mkTypeConstructor qname)

errorTypeConstructorApp =
  pp "The function type constructor `->' must be applied to exactly two types."



-- | Transforms a qualified name into a type constructor.
--   Special care is taken for primitive types which could be qualified by
--   \'Prelude\'.

mkTypeConstructor :: HsQName -> ErrorOr S.TypeConstructor
mkTypeConstructor (Qual (Module mod) hsName) = 
  if mod == "Prelude"
    then return (asCon hsName)
    else return (S.Con $ hsNameToIdentifier hsName)
mkTypeConstructor (UnQual hsName)          = return $ asCon hsName
mkTypeConstructor (Special HsUnitCon)      = return $ S.ConUnit
mkTypeConstructor (Special HsListCon)      = return $ S.ConList
mkTypeConstructor (Special (HsTupleCon n)) = return $ S.ConTuple n

-- missing case '(Special HsFunCon)' cannot occur,
-- see function 'mkTypeCOnstructorApp'

-- missing case '(Special HsCons)' cannot occur,
-- this is not valid Haskell syntax



-- | Transforms a name into a type constructor. This functions differentiates
--   between primitive types and other types.

asCon :: HsName -> S.TypeConstructor
asCon name = case name of
  HsIdent "Int"     -> S.ConInt
  HsIdent "Integer" -> S.ConInteger
  HsIdent "Float"   -> S.ConFloat
  HsIdent "Double"  -> S.ConDouble
  HsIdent "Char"    -> S.ConChar
  otherwise         -> S.Con $ hsNameToIdentifier name



-- | Transforms a Haskell name into a type variable.

mkTypeVariable :: HsName -> ErrorOr S.TypeVariable
mkTypeVariable = return . S.TV . hsNameToIdentifier



-- | Transforms a qualified Haskell name into an identifier.
--   The module part of a qualified name is ignored.
--   This function fails with an appropriate error message when applied to a
--   special Haskell constructor, i.e. a unit, list, function or tuple
--   constructor.

mkIdentifierQ :: HsQName -> ErrorOr S.Identifier
mkIdentifierQ (UnQual hsName)          = return (hsNameToIdentifier hsName)
mkIdentifierQ (Qual (Module _) hsName) = return (hsNameToIdentifier hsName)

mkIdentifierQ (Special HsUnitCon)      = throwErrorIdentifierQ "`()'"
mkIdentifierQ (Special HsListCon)      = throwErrorIdentifierQ "`[]'"
mkIdentifierQ (Special HsFunCon)       = throwErrorIdentifierQ "`->'"
mkIdentifierQ (Special HsCons)         = throwErrorIdentifierQ "`:'"
mkIdentifierQ (Special (HsTupleCon _)) = throwErrorIdentifierQ "for tuples"

throwErrorIdentifierQ s = throwError $ pp $
  "The constructor " ++ s ++ " must not be used as an identifier."



-- | Transforms a Haskell name into an identifier.
--   This function encapsulates 'hsNameToIdentifier' into the 'ErrorOr' monad.

mkIdentifier :: HsName -> ErrorOr S.Identifier
mkIdentifier = return . hsNameToIdentifier



-- | Transforms a Haskell name into an identifier.

hsNameToIdentifier :: HsName -> S.Identifier
hsNameToIdentifier = S.Ident . hsNameToString



-- | Transforms a Haskell name into a string.
--   Haskell symbols are surrounded by parentheses.

hsNameToString :: HsName -> String
hsNameToString (HsIdent s)  = s
hsNameToString (HsSymbol s) = "(" ++ s ++ ")"


