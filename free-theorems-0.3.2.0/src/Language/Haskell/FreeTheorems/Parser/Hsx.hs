module Language.Haskell.FreeTheorems.Parser.Hsx (parse) where



import Control.Monad (foldM, liftM, liftM2, when)
import Control.Monad.Error (Error (..), throwError)
import Control.Monad.Reader (ReaderT, runReaderT, local, ask)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (Writer, tell)
import Data.Generics (everywhere, mkT)
import Data.Maybe (fromMaybe)
import Data.List (nub, (\\), intersect)
import Language.Haskell.Exts.Parser (parseModule, ParseResult(..))
import Language.Haskell.Exts.Syntax
import Text.PrettyPrint

import qualified Language.Haskell.FreeTheorems.Syntax as S
import Language.Haskell.FreeTheorems.Frontend.Error




------- Main parser function --------------------------------------------------


-- | Parses a string to a list of declarations.
--   The string should contain a Haskell module.
--
--   This function is based on the extended Haskell parser of the 
--   \'haskell-src-exts\' package.
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
--   * Only type variables can be constrained by type classes. That means, for
--     example, the type @Eq [a] => [a]@ is not accepted.
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
--   * Further extensions over Haskell98 allowed by the underlying parser are
--     also forbidden, namely generalised algebraic data types and unboxed 
--     tuples.
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
    collectDeclarations :: [S.Declaration] -> Decl -> Parsed [S.Declaration]
    collectDeclarations ds d = 
      case mkDeclaration d of
        Left e   -> tell [e] >> return ds
        Right d' -> return (ds ++ [d'])
      




------- Filter declarations ---------------------------------------------------



-- | Filters all declarations of a Haskell module.

filterDeclarations :: Module -> [Decl]
filterDeclarations (Module _ _ _ _ _ _ ds) = filter isAcceptedDeclaration ds
  where
    isAcceptedDeclaration decl = case decl of
      TypeDecl _ _ _ _        -> True
      DataDecl _ _ _ _ _ _ _  -> True
      ClassDecl _ _ _ _ _ _   -> True
      TypeSig _ _ _           -> True
      otherwise               -> False



-- | Transforms a list of declarations by simplifying type signatures.

transform :: [Decl] -> [Decl]
transform = everywhere (mkT extendTypeSignature)
  where
    -- Type signatures can be given for several names at once.
    -- This function transforms declarations such that every type signature is
    -- given for exactly one name only.
    extendTypeSignature :: [Decl] -> [Decl]
    extendTypeSignature ds = case ds of
      ((TypeSig l ns t):ds') -> (map (\n -> TypeSig l [n] t) ns) ++ ds'
      otherwise                -> ds





------- Transform declarations ------------------------------------------------


-- | Transforms a class declaration.

clsDeclToDecl :: ClassDecl -> ErrorOr Decl
clsDeclToDecl decl = case decl of
  ClsDecl decl         -> return decl
  ClsDataFam _ _ _ _ _ -> throwError noDataFam
  ClsTyFam _ _ _ _     -> throwError noTypeFam
  ClsTyDef _ _ _       -> throwError noTypeFam

noDataFam   = pp "Data Families are not allowed"
noTypeFam   = pp "Type Families are not allowed"

-- | Transforms a declaration.

mkDeclaration :: Decl -> ErrorOr S.Declaration
mkDeclaration decl = case decl of
  TypeDecl l n vs t                -> do
                                        ns <- sequence (map unkind vs) 
                                        addErr l n (mkType n ns t)
  DataDecl l DataType _ n vs cs _  -> do
                                        ns <- sequence (map unkind vs) 
                                        addErr l n (mkData n ns cs)
  DataDecl l NewType  _ n vs [c] _ -> do
                                        ns <- sequence (map unkind vs) 
                                        addErr l n (mkNewtype n ns c)
  ClassDecl l scs n [v] _ ds       -> do
                                        nv <- unkind v 
                                        addErr l n (mkClass scs n nv ds)
  TypeSig l [n] t                  -> addErr l n (mkSignature n t)

  ClassDecl l _ n [] _ _           -> addErr l n (throwError missingVar)
  ClassDecl l _ n (_:_:_) _ _      -> addErr l n (throwError noMultiParam)

  -- no other case con occur, see above function 'filterDeclarations'. 
  where 
    unkind (UnkindedVar x) = return x
    unkind _               = throwError $ pp "Type variable declarations with explicit kind annotations are not allowed."


missingVar   = pp "Missing type variable to be constrained by the type class."
noMultiParam = pp "Multi-parameter type classes are not allowed."



-- | Adds an error message based on the name of a declaration if the given
--   transformation caused an error.

addErr :: SrcLoc -> Name -> ErrorOr S.Declaration-> ErrorOr S.Declaration
addErr loc name e = case getError e of
  Nothing  -> e
  Just doc -> throwError $
                pp ("In the declaration of `" ++ hsNameToString name 
                    ++ "' at (" ++ show (srcLine loc) ++ ":" 
                    ++ show (srcColumn loc) ++ "):")
                $$ nest 2 doc



-- | Transforms the components of a type declaration.

mkType :: Name -> [Name] -> Type -> ErrorOr S.Declaration
mkType name vars ty = do
  ident <- mkIdentifier name
  tvs   <- mapM mkTypeVariable vars
  t     <- mkTypeExpression ty
  return (S.TypeDecl (S.Type ident tvs t))



-- | Transforms the components of a data declaration.

mkData :: Name -> [Name] -> [QualConDecl] -> ErrorOr S.Declaration
mkData name vars cons = do
  ident <- mkIdentifier name
  tvs   <- mapM mkTypeVariable vars
  ds    <- mapM mkDataConstructorDeclaration cons
  return (S.DataDecl (S.Data ident tvs ds))
       


-- | Transforms a data constructor declaration.

mkDataConstructorDeclaration :: 
    QualConDecl -> ErrorOr S.DataConstructorDeclaration

mkDataConstructorDeclaration (QualConDecl _ _ _ (ConDecl name btys)) =
  mkDataConDecl name btys

mkDataConstructorDeclaration (QualConDecl _ _ _ (RecDecl name rbtys)) =
  let btys = concatMap (\(l,ty) -> replicate (length l) ty) rbtys
   in mkDataConDecl name btys
  


-- | Transforms the components of a data constructor declaration.

mkDataConDecl ::
    Name 
    -> [BangType] 
    -> ErrorOr S.DataConstructorDeclaration

mkDataConDecl name btys = do
  ident <- mkIdentifier name
  bts   <- mapM mkBangTyEx btys
  return (S.DataCon ident bts)
  where
    mkBangTyEx (BangedTy ty)   = liftM S.Banged   (mkTypeExpression ty)
    mkBangTyEx (UnBangedTy ty) = liftM S.Unbanged (mkTypeExpression ty)



-- | Transforms the components of a newtype declaration.

mkNewtype :: Name -> [Name] -> QualConDecl -> ErrorOr S.Declaration
mkNewtype name vars (QualConDecl _ _ _ con) = do
  ident   <- mkIdentifier name
  tvs     <- mapM mkTypeVariable vars
  (con,t) <- mkNewtypeConDecl con
  return (S.NewtypeDecl (S.Newtype ident tvs con t))
  where
    mkNewtypeConDecl (ConDecl c bts) = mkNCD c bts
    mkNewtypeConDecl (RecDecl c bts) = mkNCD c (snd $ unzip bts)

    mkNCD c [bty] = liftM2 (,) (mkIdentifier c) (bang bty)
    mkNCD c []      = throwError errNewtype
    mkNCD c (_:_:_) = throwError errNewtype

    errNewtype = 
      pp "A `newtype' declaration must have exactly one type expression."

    bang (UnBangedTy ty) = mkTypeExpression ty
    bang (BangedTy ty)   = 
      throwError (pp "A `newtype' declaration must not use a strictness flag.")



-- | Transforms the components of a Haskell class declaration.
--   Every declaration in the class body is ignored except of type signatures.

mkClass :: Context -> Name -> Name -> [ClassDecl] -> ErrorOr S.Declaration
mkClass ctx name var clsDecls = do
  ident   <- mkIdentifier name
  tv      <- mkTypeVariable var
  superCs <- mkContext ctx >>= check tv
  decls   <- mapM clsDeclToDecl clsDecls 
  sigs    <- liftM (map toSig) (mapM mkDeclaration (filter isSig decls))
    -- mapping 'isSig' is safe because after applying 'filter' no other
    -- declarations are left except of type signatures

  return (S.ClassDecl (S.Class superCs ident tv sigs))
  where
    -- Returns 'True' if a declaration is a type signature, otherwise 'False'.
    isSig :: Decl -> Bool
    isSig decl = case decl of
      TypeSig _ _ _ -> True
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

mkSignature :: Name -> Type -> ErrorOr S.Declaration
mkSignature var ty = do
  ident   <- mkIdentifier var
  t       <- mkTypeExpression ty
  return $ S.TypeSig (S.Signature ident t)



-- | Transforms a Haskell context.
--   If the context contains not only variables, but also more complex types,
--   this function fails with an appropriate error message.

mkContext :: Context -> ErrorOr [(S.TypeClass, S.TypeVariable)]
mkContext = mapM trans
  where
    trans (ClassA qname [TyVar var]) = do
      ident <- liftM S.TC (mkIdentifierQ qname)
      tv    <- mkTypeVariable var
      return $ (ident, tv) 
    
    trans (ClassA _ _) = throwError errContext
    trans (IParam _ _) = throwError errImplicit

errContext =
  pp "Only a type variable may be constrained by a class in a context."

errImplicit = 
  pp "Implicit parameters are not allowed." 




------- Transform type expressions --------------------------------------------



type EnvErrorOr a = ReaderT [S.TypeVariable] (Either Doc) a



mkTypeExpression :: Type -> ErrorOr S.TypeExpression
mkTypeExpression ty = runReaderT (mkTypeExpressionT ty) []



-- | Transforms a Haskell type.
--   Note that a type variable is not allowed to be applied to some type.

mkTypeExpressionT :: Type -> EnvErrorOr S.TypeExpression
mkTypeExpressionT (TyVar var)     = liftM S.TypeVar 
                                            (lift (mkTypeVariable var))
mkTypeExpressionT (TyApp ty1 ty2) = lift (mkAppTyEx ty1 [ty2])
mkTypeExpressionT (TyCon qname)   = lift (mkTypeConstructorApp qname [])

mkTypeExpressionT (TyInfix ty1 qname ty2) = -- infix type constructor
  mkTypeExpressionT (TyApp (TyApp (TyCon qname) ty1) ty2)

mkTypeExpressionT (TyFun ty1 ty2) = do
  t1 <- mkTypeExpressionT ty1
  t2 <- mkTypeExpressionT ty2
  return (S.TypeFun t1 t2)

mkTypeExpressionT (TyTuple Boxed tys)   = do
  ts <- mapM mkTypeExpressionT tys
  return (S.TypeCon (S.ConTuple (length ts)) ts)

mkTypeExpressionT (TyForall maybeVars ctx ty) =
  mkForallTyEx (maybe [] (map unKind) maybeVars) ctx ty
  where unKind (KindedVar n _) = n
        unKind (UnkindedVar n) = n

--- daniel
mkTypeExpressionT (TyList ty) = do
  t <- mkTypeExpressionT ty
  return (S.TypeCon (S.ConList) [t])

mkTypeExpressionT (TyParen ty) = mkTypeExpressionT ty

mkTypeExpressionT (TyKind ty kd) = 
    throwError (pp "Explicit kind signatures are not allowed.")

-- mkTypeExpressionT (TyPred _) = 
--   throwError (pp "Implicit parameters are not allowed.")

mkTypeExpressionT (TyTuple Unboxed _ ) = 
  throwError (pp "Unboxed tuples are not allowed.")



-- | Checks type abstractions for unique variables, merges the contexts and
--   creates a type expression.

mkForallTyEx :: [Name] -> Context -> Type -> EnvErrorOr S.TypeExpression
mkForallTyEx vars ctx ty = do
  vs <- unique vars
  cx <- lift (mkContext ctx)
  let unboundVars = (nub . snd . unzip $ cx) \\ vs
  let allVars = vs ++ unboundVars
  knownVars <- ask
  let errVars = knownVars `intersect` unboundVars
  when (not (null errVars)) $ throwError $ pp $ 
    "The constrained type variable `" ++ (S.unpackIdent . (\(S.TV i) -> i) . head $ errVars)
    ++ "' must be explicitly quantified."
  liftM (merge allVars cx) (local (++ allVars) (mkTypeExpressionT ty))
  where
    -- Checks if the elements of the argument are unique, and throws an error
    -- otherwise.
    unique :: [Name] -> EnvErrorOr [S.TypeVariable]
    unique []     = return []
    unique (v:vs) = if v `elem` vs
                      then throwError (pp $
                             "Conflicting type variables in a type "
                             ++ "abstraction, the type variable `"
                             ++ hsNameToString v ++ "' is quantified more "
                             ++ "than once.")
                      else liftM2 (:) (lift (mkTypeVariable v)) (unique vs)

    -- Merges the context and the type expression. The context is represented
    -- as type abstractions.
    merge :: 
        [S.TypeVariable] -> [(S.TypeClass, S.TypeVariable)] 
        -> S.TypeExpression -> S.TypeExpression
    merge vs cx t = foldr (\v -> S.TypeAbs v (classes cx v)) t vs

    -- Returns classes constraining v.
    classes cx v = nub (map fst (filter ((==) v . snd) cx))



-- | Collects applied types and transforms them into a type expression.

mkAppTyEx :: Type -> [Type] -> ErrorOr S.TypeExpression
mkAppTyEx ty tys = case ty of
  TyFun _ _   -> throwError $ pp ("A function type must not be applied to a "
                                    ++ "type.")
  TyTuple _ _ -> throwError (pp "A tuple type must not be applied to a type.")
  TyVar _     -> throwError (pp "A variable must not be applied to a type.")
  TyApp t1 t2 -> mkAppTyEx t1 (t2 : tys)
  TyCon qname -> mapM mkTypeExpression tys >>= mkTypeConstructorApp qname 



-- | Interprets a qualified name as a type constructor and applies it to a list
--   of type expressions.
--   The function type constructor is handled specially because it has to have
--   exactly two arguments.

mkTypeConstructorApp :: 
    QName 
    -> [S.TypeExpression] 
    -> ErrorOr S.TypeExpression

mkTypeConstructorApp (Special FunCon) [t1,t2] = return $ S.TypeFun t1 t2
mkTypeConstructorApp (Special FunCon) _       = throwError errorTypeConstructorApp

mkTypeConstructorApp qname              ts      = 
  liftM (\con -> S.TypeCon con ts) (mkTypeConstructor qname)

errorTypeConstructorApp =
  pp "The function type constructor `->' must be applied to exactly two types."



-- | Transforms a qualified name into a type constructor.
--   Special care is taken for primitive types which could be qualified by
--   \'Prelude\'.

mkTypeConstructor :: QName -> ErrorOr S.TypeConstructor
mkTypeConstructor (Qual (ModuleName mod) hsName) = 
  if mod == "Prelude"
    then return (asCon hsName)
    else return (S.Con $ hsNameToIdentifier hsName)
mkTypeConstructor (UnQual hsName)                = return $ asCon hsName
mkTypeConstructor (Special UnitCon)              = return $ S.ConUnit
mkTypeConstructor (Special ListCon)              = return $ S.ConList
mkTypeConstructor (Special (TupleCon Boxed n))   = return $ S.ConTuple n
mkTypeConstructor (Special (TupleCon Unboxed n)) = throwError $ pp "Unboxed tuples are not allowed."

-- missing case '(Special FunCon)' cannot occur,
-- see function 'mkTypeCOnstructorApp'

-- missing case '(Special Cons)' cannot occur,
-- this is not valid Haskell syntax



-- | Transforms a name into a type constructor. This functions differentiates
--   between primitive types and other types.

asCon :: Name -> S.TypeConstructor
asCon name = case name of
  Ident "Int"     -> S.ConInt
  Ident "Integer" -> S.ConInteger
  Ident "Float"   -> S.ConFloat
  Ident "Double"  -> S.ConDouble
  Ident "Char"    -> S.ConChar
  otherwise         -> S.Con $ hsNameToIdentifier name



-- | Transforms a Haskell name into a type variable.

mkTypeVariable :: Name -> ErrorOr S.TypeVariable
mkTypeVariable = return . S.TV . hsNameToIdentifier



-- | Transforms a qualified Haskell name into an identifier.
--   The module part of a qualified name is ignored.
--   This function fails with an appropriate error message when applied to a
--   special Haskell constructor, i.e. a unit, list, function or tuple
--   constructor.

mkIdentifierQ :: QName -> ErrorOr S.Identifier
mkIdentifierQ (UnQual hsName)          = return (hsNameToIdentifier hsName)
mkIdentifierQ (Qual (ModuleName _) hsName) = return (hsNameToIdentifier hsName)

mkIdentifierQ (Special UnitCon)            = throwErrorIdentifierQ "`()'"
mkIdentifierQ (Special ListCon)            = throwErrorIdentifierQ "`[]'"
mkIdentifierQ (Special FunCon)             = throwErrorIdentifierQ "`->'"
mkIdentifierQ (Special Cons)               = throwErrorIdentifierQ "`:'"
mkIdentifierQ (Special (TupleCon _ _)) = throwErrorIdentifierQ "for tuples"

throwErrorIdentifierQ s = throwError $ pp $
  "The constructor " ++ s ++ " must not be used as an identifier."



-- | Transforms a Haskell name into an identifier.
--   This function encapsulates 'hsNameToIdentifier' into the 'ErrorOr' monad.

mkIdentifier :: Name -> ErrorOr S.Identifier
mkIdentifier = return . hsNameToIdentifier



-- | Transforms a Haskell name into an identifier.

hsNameToIdentifier :: Name -> S.Identifier
hsNameToIdentifier = S.Ident . hsNameToString



-- | Transforms a Haskell name into a string.
--   Haskell symbols are surrounded by parentheses.

hsNameToString :: Name -> String
hsNameToString (Ident s)  = s
hsNameToString (Symbol s) = "(" ++ s ++ ")"



