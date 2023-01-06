


-- | Defines local checks, i.e. checks which only look at one declaration at a
--   time.

module Language.Haskell.FreeTheorems.Frontend.CheckLocal (
    checkLocal
  , checkDataAndNewtypeDeclarations
) where



import Data.Generics (Data, everything, mkQ)
import Data.List (group, sort)
import Data.Maybe (mapMaybe, fromJust, isJust)
import qualified Data.Set as Set
    ( Set, union, empty, difference, fromList, null, elems, isSubsetOf
    , singleton)

import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.Frontend.Error
import Language.Haskell.FreeTheorems.Frontend.TypeExpressions





------- Local checks ----------------------------------------------------------


-- | Check validity of every declaration.
--   This includes ensuring that fixed type expressions occur nowhere, that only
--   declared type variables occur in right-hand sides and that no primitive
--   type is declared, among other restrictions.
--
--   Local checks comprise all those which can be down by just looking at a
--   single declaration.

checkLocal :: [Declaration] -> Checked [Declaration]
checkLocal = foldChecks checkDecl
  where
    checkDecl :: Declaration -> ErrorOr ()
    checkDecl (DataDecl d)    = checkDataDecl d
    checkDecl (NewtypeDecl d) = checkNewtypeDecl d
    checkDecl (TypeDecl d)    = checkTypeDecl d
    checkDecl (ClassDecl d)   = checkClassDecl d
    checkDecl (TypeSig sig)   = checkSignature sig



-- | Checks a @data@ declaration. The following restrictions must hold:
--   
--   * The declared type constructor is not a primitive type.
--   * The variables occurring on the right-hand side have to be mentioned on
--     the left-hand side, and the left-hand side variables are pairwise
--     distinct.
--   * The declaration is not nested, i.e. if the declared type constructor
--     occurs on the right-hand side, it has only type variables as arguments.
--   * No fixed type expression occurs in any type expression.

checkDataDecl :: DataDeclaration -> ErrorOr ()
checkDataDecl d =
  inDecl (DataDecl d) $ do
    checkNotPrimitive (dataName d)
    checkVariables (dataVars d)
                   (everything Set.union
                      (Set.empty `mkQ` (freeTypeVariables . withoutBang)) 
                      (dataCons d))
    checkNotEmpty (dataCons d)
    mapM_ (checkNotNested (dataName d) (map TypeVar (dataVars d)))
          (conNamesAndTypes d)
    mapM_ (checkNoFixedTEsNamed "data constructor") (conNamesAndTypes d)
  where
    conNamesAndTypes = 
      map (makePair dataConName (map withoutBang . dataConTypes)) . dataCons



-- | Checks a @newtype@ declaration. The following restrictions must hold:
--   
--   * The declared type constructor is not a primitive type.
--   * The variables occurring on the right-hand side have to be mentioned on
--     the left-hand side, and the left-hand side variables are pairwise
--     distinct.
--   * The declaration is not nested, i.e. if the declared type constructor
--     occurs on the right-hand side, it has only type variables as arguments.
--   * No fixed type expression occurs in the right-hand side type expression.

checkNewtypeDecl :: NewtypeDeclaration -> ErrorOr ()
checkNewtypeDecl d =
  inDecl (NewtypeDecl d) $ do
    checkNotPrimitive (newtypeName d)
    checkVariables (newtypeVars d) (freeTypeVariables $ newtypeRhs d)
    checkNotNested (newtypeName d) (map TypeVar (newtypeVars d)) (conAndType d)
    checkNoFixedTEsNamed "data constructor" (conAndType d)
  where
    conAndType = makePair newtypeCon (singletonList . newtypeRhs)



-- | Checks a @type@ declaration. The following restrictions must hold:
--   
--   * The declared type constructor is not a primitive type.
--   * The variables occurring on the right-hand side have to be mentioned on
--     the left-hand side, and the left-hand side variables are pairwise
--     distinct.
--   * The declaration must not be recursive, i.e. the type constructor declared
--     by this declaration must not occur on th right-hand side.
--   * No fixed type expression occurs in the right-hand side type expression.

checkTypeDecl :: TypeDeclaration -> ErrorOr ()
checkTypeDecl d = 
  inDecl (TypeDecl d) $ do
    checkNotPrimitive (typeName d)
    checkVariables (typeVars d) (freeTypeVariables $ typeRhs d)
    checkTypeDeclNotRecursive (typeName d) (typeRhs d)
    checkNoFixedTEs (typeRhs d)



-- | Checks a @class@ declaration. The following restrictions must hold:
--   
--   * The declared type class does not equal a primitive type.
--   * The names of the class methods are pairwise distinct. 
--   * The class variable occurs in the type expression of every class method.
--   * The name of the class does not occur in a type expression of any class
--     method.
--   * No fixed type expression occurs in a type expression of any class method.

checkClassDecl :: ClassDeclaration -> ErrorOr ()
checkClassDecl d =
  inDecl (ClassDecl d) $ do
    checkNotPrimitive (className d)
    checkClassMethodsDistinct (map signatureName . classFuns $ d)
    checkClassVarInMethods (classVar d) (classFuns d)
    checkClassDeclNotRecursive (className d) (classFuns d)
    mapM_ (checkNoFixedTEsNamed "class method")
          (map (makePair signatureName (singletonList . signatureType))
               (classFuns d))



-- | Checks a type signature. The following restrictions must hold:
--   
--   * No fixed type expressions occurs in the type expression of this type
--     signature.

checkSignature :: Signature -> ErrorOr ()
checkSignature s =
  inDecl (TypeSig s) $ do
    checkNoFixedTEs (signatureType s)





------- Special checks for data and newtype declarations ----------------------


-- | Check data and newtype declarations for occurring function type
--   constructors or type abstraction constructors. If any declaration contains
--   one of these, an error message is created. All other declarations are
--   passed.

checkDataAndNewtypeDeclarations :: [Declaration] -> Checked [Declaration]
checkDataAndNewtypeDeclarations = foldChecks checkDN
  where
    checkDN :: Declaration -> ErrorOr ()
    checkDN d = case d of
      DataDecl d'    -> inDecl d (mapM_ checkAbsFun (dataConsAndTypes d'))
      NewtypeDecl d' -> inDecl d (checkAbsFun (newtypeConAndType d'))
      otherwise      -> return ()

    dataConsAndTypes =
      map (makePair dataConName (map withoutBang . dataConTypes)) . dataCons
    
    newtypeConAndType = makePair newtypeCon (singletonList . newtypeRhs)






------- Checking restrictions -------------------------------------------------


-- | Checks if the given identifier is not a name of a primitive type.
--   Otherwise, an error message is created.

checkNotPrimitive :: Identifier -> ErrorOr ()
checkNotPrimitive (Ident name) =
  errorIf (name `elem` ["Int", "Integer", "Float", "Double", "Char"]) $
    pp ("A primitive type must not have a declaration.")
  


-- | Checks if the second argument set is contained in the first argument list.
--   If not, an error message is returned.
--
--   Checks also if first argument contains pairwise distinct variables.
--   If not, an error message is returned.

checkVariables :: [TypeVariable] -> Set.Set TypeVariable -> ErrorOr ()
checkVariables vs rvs = do
  let es = extractRepeatingElements vs
  errorIf (not $ null es) $
    pp ("Type variables must not be given more than once on the left-hand "
        ++ "side of a declaration. "
        ++ violating "variable" (map varName $ es))

  let set = rvs `Set.difference` Set.fromList vs
  errorIf (not (Set.null set)) $
    pp ("Type variables occurring on the right-hand side of a declaration must "
        ++ "be declared on the left-hand side. "
        ++ violating "variable" (map varName . Set.elems $ set))

  where
    varName (TV v) = unpackIdent v



-- | Checks that there is at least one data constructor declaration in the the
--   declaration of an algebraic data type.

checkNotEmpty :: [DataConstructorDeclaration] -> ErrorOr ()
checkNotEmpty cons =
  errorIf (null cons) $
    pp ("The declaration of an algebraic data type must have at least one "
        ++ "data constructor.")



-- | Checks if the identifiers occurs in any of the given type expressions as
--   a type constructor. If so, and if the identifier is applied not only to
--   type variables, it is called nested and an error message is created.

checkNotNested :: 
    Identifier -> [TypeExpression] -> (Identifier, [TypeExpression]) 
    -> ErrorOr ()
checkNotNested con vs (dcon, ts) =
  errorIf (any (satisfiesSomewhere isNested) ts) $
    pp ("Declarations must not be nested."
        ++ violating "data constructor" [unpackIdent dcon])
  where
    isNested t = case t of
      TypeCon (Con c) ts -> c == con && ts /= vs
      otherwise          -> False



-- | Checks if a type declaration is recursive, i.e. the identifier occurs in
--   the given type expression as a type constructor.
--   If so, an error message is created.

checkTypeDeclNotRecursive :: Identifier -> TypeExpression -> ErrorOr ()
checkTypeDeclNotRecursive ident t =
  errorIf (satisfiesSomewhere (isCon ident) t) $
    pp ("A type synonym must not be declared recursively.")
  where
    isCon ident t = case t of
      TypeCon (Con c) _ -> c == ident
      otherwise         -> False



-- | Checks that the names of class methods are pairwise distinct.
--   If not, an error message is created.

checkClassMethodsDistinct :: [Identifier] -> ErrorOr ()
checkClassMethodsDistinct is =
  let es = extractRepeatingElements is
   in errorIf (not $ null es) $
        pp ("Class methods must not be declared more than once. "
            ++ violating "class method" (map unpackIdent es))



-- | Checks if the given identifier occurs as free type variable in every
--   signature. If not, an error message is created.

checkClassVarInMethods :: TypeVariable -> [Signature] -> ErrorOr ()
checkClassVarInMethods v@(TV vName) ss =
  let setOfv      = Set.singleton v
      vIsFreeIn t = setOfv `Set.isSubsetOf` freeTypeVariables t
      ms          = filter (not . vIsFreeIn . signatureType) ss
   in errorIf (not $ null ms) $
        pp ("The type variable `" ++ unpackIdent vName ++ "' must occur free "
            ++ "in the type expressions of every class method. "
            ++ violating "class method" (map (unpackIdent . signatureName) ms))
    


-- | Checks that the name of a type class does not occur in any of the class
--   methods. Otherwise, an error message is created.
checkClassDeclNotRecursive :: Identifier -> [Signature] -> ErrorOr ()
checkClassDeclNotRecursive ident sigs =
  let hasThisClass = satisfiesSomewhere (\c -> c == TC ident)
      ms           = filter (hasThisClass . signatureType) sigs
   in errorIf (not $ null ms) $
        pp ("The type class `" ++ unpackIdent ident ++ "' must not occur in a "
            ++ "type expression of any class method of this class. "
            ++ violating "class method" (map (unpackIdent . signatureName) ms))



-- | Checks that no FixedTypeExpression occurs in the given list of named
--   type expressions. The first argument is used in generating a helpful error
--   message and describes what kind of items the second argument contains.

checkNoFixedTEsNamed :: String -> (Identifier, [TypeExpression]) -> ErrorOr ()
checkNoFixedTEsNamed tag (con, ts) =
  let es = mapMaybe checkNoFixedTEsPlain ts
   in errorIf (not . null $ es) $
        pp (head es ++ violating tag [unpackIdent con])



-- | Checks that no FixedTypeExpression occurs in a type expression.
--   If it does, an error message is created.

checkNoFixedTEs :: TypeExpression -> ErrorOr ()
checkNoFixedTEs t = 
  let e = checkNoFixedTEsPlain t
   in errorIf (isJust e) (pp . fromJust $ e)
  


-- | Returns an error if a FixedTypeExpression occurs in the argument, otherwise
--   returns @Nothing@.

checkNoFixedTEsPlain :: TypeExpression -> Maybe String
checkNoFixedTEsPlain t =
  if (satisfiesSomewhere isFixedTE t)
    then Just "A fixed type expression must not occur in a type expression."
    else Nothing
  where
    isFixedTE t = case t of
      TypeExp _ -> True
      otherwise -> False



-- | Checks that no function type constructor and no type abstraction
--   constructor occur in the given named list of type expressions.

checkAbsFun :: (Identifier, [TypeExpression]) -> ErrorOr ()
checkAbsFun (con, ts) =
  errorIf (satisfiesSomewhere isAbsOrFun ts) $
    pp ("Algebraic data types and type renamings must be declared without type "
        ++ "abstractions and function type constructors occurring on the "
        ++ "right-hand side."
        ++ violating "data constructor" [unpackIdent con])
  where
    isAbsOrFun t = case t of
      TypeFun _ _   -> True
      TypeAbs _ _ _ -> True
      otherwise     -> False





------- Helper functions ------------------------------------------------------


-- | Applies two functions to a value and creates a pair of the results.

makePair :: (a -> b) -> (a -> c) -> a -> (b, c)
makePair f g x = (f x, g x)


-- | Creates a list containing just one element.

singletonList :: a -> [a]
singletonList x = [x]



-- | Filters all elements which occur more than once in the given list.
--   Only one representative is returned for every group of equal items.

extractRepeatingElements :: Ord a => [a] -> [a]
extractRepeatingElements =
  map head . filter (\vs -> length vs > 1) . group . sort



-- | Tests if a predicate holds somewhere in an arbitrary tree.

satisfiesSomewhere :: (Data a, Data b) => (a -> Bool) -> b -> Bool
satisfiesSomewhere predicate x = everything (||) (False `mkQ` predicate) x





