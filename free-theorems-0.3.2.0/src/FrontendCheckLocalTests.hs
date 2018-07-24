


module FrontendCheckLocalTests (tests) where



import Control.Monad.Writer (runWriter)
import Data.Generics (Typeable, Data, everything, mkQ)
import Data.List (nub)
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.Set as Set
    (Set, empty, union, fromList, isSubsetOf, member, singleton)
import Test.QuickCheck

import Tests

import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.Frontend
import Language.Haskell.FreeTheorems.Frontend.Error
import Language.Haskell.FreeTheorems.Frontend.TypeExpressions
import Language.Haskell.FreeTheorems.Frontend.CheckLocal
import Language.Haskell.FreeTheorems.Frontend.CheckGlobal



-- | Runs all tests.

tests :: IO ()
tests = do

  doTest "check local data free variables" prop_checkLocalDataFreeVars
  doTest "check local data distinct variables" prop_checkLocalDataVars
  doTest "check local data not primitive" prop_checkLocalDataNotPrim
  doTest "check local data no fixed types" prop_checkLocalDataNoFixedTEs
  doTest "check local data has data constructor" prop_checkLocalDataNotEmpty
  doTest "check local data not nested" prop_checkLocalDataNotNested
  doTest "check local data no function nor abstraction"
    prop_checkLocalDataAbsFun

  doTest "check local newtype free variables" prop_checkLocalNewtypeFreeVars
  doTest "check local newtype distinct variables" prop_checkLocalNewtypeVars
  doTest "check local newtype not primitive" prop_checkLocalNewtypeNotPrim
  doTest "check local newtype no fixed types" prop_checkLocalNewtypeNoFixedTEs
  doTest "check local newtype not nested" prop_checkLocalNewtypeNotNested
  doTest "check local newtype no function nor abstraction"
    prop_checkLocalNewtypeAbsFun

  doTest "check local type free variables" prop_checkLocalTypeFreeVars
  doTest "check local type distinct variables" prop_checkLocalTypeVars
  doTest "check local type not primitive" prop_checkLocalTypeNotPrim
  doTest "check local type no fixed types" prop_checkLocalTypeNoFixedTEs
  doTest "check local type not nested" prop_checkLocalTypeNotNested

  doTest "check local class methods distinct"
    prop_checkLocalClassMethodsDistinct
  doTest "check local class variable is free in methods"
    prop_checkLocalClassFreeVar
  doTest "check local class not recursive" prop_checkLocalClassNotRecursive
  doTest "check local class not primitive" prop_checkLocalClassNotPrim
  doTest "check local class no fixed types" prop_checkLocalClassNoFixedTEs

  doTest "check local signature no fixed types"
    prop_checkLocalSignatureNoFixedTEs

   




------- Test local checks -----------------------------------------------------


-- | Property: Checks in data declarations that free variables of the right-hand
--   side are declared on the left-hand side.

prop_checkLocalDataFreeVars d = 
  checkInData d $ \d' ->
    allFreeVars (dataCons d') `Set.isSubsetOf` Set.fromList (dataVars d')
  where
    allFreeVars :: (Typeable a, Data a) => a -> Set.Set TypeVariable
    allFreeVars = everything (Set.union) (Set.empty `mkQ` freeVars)

    freeVars :: BangTypeExpression -> Set.Set TypeVariable
    freeVars = freeTypeVariables . withoutBang



-- | Property: Checks in data declarations that the left-hand side variables are
--   pairwise distinct.

prop_checkLocalDataVars d =
  checkInData d $ \d' ->
    length (nub (dataVars d')) == length (dataVars d')



-- | Property: Checks in data declarations that the declared type constructor is
--   not a primitive type.

prop_checkLocalDataNotPrim d =
  checkInData d $ \d' ->
    isNotPrimitive (dataName d')



-- | Property: Checks in data declarations that no FixedTypeExpression occurs
--   anywhere.

prop_checkLocalDataNoFixedTEs d =
  checkInData d $ \d' ->
    not (hasFixedTypeExpressions d')



-- | Property: Checks that data declarations have at least one data constructor.

prop_checkLocalDataNotEmpty d =
  checkInData d $ \d' ->
    not (null (dataCons d'))



-- | Property: Checks that data declarations are not nested.

prop_checkLocalDataNotNested d =
  checkInData d $ \d' ->
    not (isNested (dataName d') (dataCons d'))



-- | Property: Checks in newtype declarations that variables of the right-hand
--   side are declared on the left-hand side.

prop_checkLocalNewtypeFreeVars d =
  checkInNewtype d $ \d' ->
    freeTypeVariables (newtypeRhs d') 
        `Set.isSubsetOf` Set.fromList (newtypeVars d')



-- | Property: Checks in newtype declarations that left-hand side variables
--   are pairwise distinct.

prop_checkLocalNewtypeVars d =
  checkInNewtype d $ \d' ->
    length (nub (newtypeVars d')) == length (newtypeVars d')



-- | Property: Checks in newtype declarations that the declared type constructor
--   is not equal to the name of a primitive type.

prop_checkLocalNewtypeNotPrim d =
  checkInNewtype d $ \d' ->
    isNotPrimitive (newtypeName d')



-- | Property: Checks in newtype declarations that no FixedTypeExpression 
--   occurs.

prop_checkLocalNewtypeNoFixedTEs d =
  checkInNewtype d $ \d' ->
    not (hasFixedTypeExpressions d')



-- | Property: Checks that newtype declarations are not nested.

prop_checkLocalNewtypeNotNested d =
  checkInNewtype d $ \d' ->
    not (isNested (newtypeName d') (newtypeRhs d'))



-- | Property: Checks in type declarations that variables of the right-hand
--   side are declared on the left-hand side.

prop_checkLocalTypeFreeVars d =
  checkInType d $ \d' ->
    freeTypeVariables (typeRhs d') `Set.isSubsetOf` Set.fromList (typeVars d')



-- | Property: Checks in type declarations that left-hand side variables
--   are pairwise distinct.

prop_checkLocalTypeVars d =
  checkInType d $ \d' ->
    length (nub (typeVars d')) == length (typeVars d')



-- | Property: Checks in type declarations that the declared type constructor
--   is not equal to the name of a primitive type.

prop_checkLocalTypeNotPrim d =
  checkInType d $ \d' ->
    isNotPrimitive (typeName d')



-- | Property: Checks in type declarations that no FixedTypeExpression 
--   occurs.

prop_checkLocalTypeNoFixedTEs d =
  checkInType d $ \d' ->
    not (hasFixedTypeExpressions d')



-- | Property: Checks that type declarations are not recursive.

prop_checkLocalTypeNotNested d =
  checkInType d $ \d' ->
    not (isRecursive (typeName d') (typeRhs d'))



-- | Property: Checks in class declarations that the class methods have pairwise
--   distinct names.

prop_checkLocalClassMethodsDistinct d =
  checkInClass d $ \d' ->
    let methodNames = map signatureName (classFuns d')
     in length (nub methodNames) == length methodNames



-- | Property: Checks in class declarations that the class variable occurs free
--   in all class method types.

prop_checkLocalClassFreeVar d =
  checkInClass d $ \d' ->
    let set = Set.singleton (classVar d')
     in all (\t -> (classVar d') `Set.member` freeTypeVariables t)
            (map signatureType (classFuns d'))



-- | Property: Checks in class declarations that the class name does not occur
--   in a type expression of any class method.

prop_checkLocalClassNotRecursive d =
  checkInClass d $ \d' ->
    not (isRecursive (className d') (classFuns d'))    



-- | Property: Checks in class declarations that the declared class name
--   is not equal to the name of a primitive type.

prop_checkLocalClassNotPrim d =
  checkInClass d $ \d' ->
    isNotPrimitive (className d')



-- | Property: Checks in class declarations that no FixedTypeExpression 
--   occurs.

prop_checkLocalClassNoFixedTEs d =
  checkInClass d $ \d' ->
    not (hasFixedTypeExpressions d')



-- | Property: Checks in type signatures that no FixedTypeExpression occurs.

prop_checkLocalSignatureNoFixedTEs d =
  checkInSignature d $ \d' ->
    not (hasFixedTypeExpressions d')



-- | Property: Checks in data declarations that there is no type abstraction
--   and no function type constructor.

prop_checkLocalDataAbsFun d = prop_checkAbsFun [DataDecl d] forcedCheck
  where types = d :: DataDeclaration



-- | Property: Checks in newtype declarations that there is no type abstraction
--   and no function type constructor.

prop_checkLocalNewtypeAbsFun d = prop_checkAbsFun [NewtypeDecl d] forcedCheck
  where types = d :: NewtypeDeclaration



-- | Helper function to check that a value does not contain type abstractions
--   nor function type constructors.

prop_checkAbsFun d test = test hasNoAbsNorFun . runCheck $ d
  where
    runCheck = fst . runWriter . checkDataAndNewtypeDeclarations
    
    hasNoAbsNorFun = everything (&&) (True `mkQ` noAbsFun)
    
    noAbsFun t = case t of
      TypeFun _ _   -> False
      TypeAbs _ _ _ -> False
      otherwise     -> True





-- Test helper functions ------------------------------------------------------


-- | Runs a local check on a data declaration.

checkInData :: DataDeclaration -> (DataDeclaration -> Bool) -> Property
checkInData d prop = 
  trivialCheck prop . mapMaybe toData . runLocalCheck $ [DataDecl d]
  where
    toData d = case d of { DataDecl d' -> Just d' ; otherwise -> Nothing }



-- | Runs a local check on a newtype declaration.

checkInNewtype :: NewtypeDeclaration -> (NewtypeDeclaration -> Bool) -> Property
checkInNewtype d prop =
  forcedCheck prop . mapMaybe toNewtype . runLocalCheck $ [NewtypeDecl d]
  where
    toNewtype d = case d of { NewtypeDecl d' -> Just d' ; otherwise -> Nothing }



-- | Runs a local check on a type declaration.

checkInType :: TypeDeclaration -> (TypeDeclaration -> Bool) -> Property
checkInType d prop = 
  forcedCheck prop . mapMaybe toType . runLocalCheck $ [TypeDecl d]
  where
    toType d = case d of { TypeDecl d' -> Just d' ; otherwise -> Nothing }



-- | Runs a local check on a class declaration.

checkInClass :: ClassDeclaration -> (ClassDeclaration -> Bool) -> Property
checkInClass d prop = 
  forcedCheck prop . mapMaybe toClass . runLocalCheck $ [ClassDecl d]
  where
    toClass d = case d of { ClassDecl d' -> Just d' ; otherwise -> Nothing }



-- | Runs a local check on a type signature.

checkInSignature :: Signature -> (Signature -> Bool) -> Property
checkInSignature d prop = 
  forcedCheck prop . mapMaybe toSig . runLocalCheck $ [TypeSig d]
  where
    toSig d = case d of { TypeSig d' -> Just d' ; otherwise -> Nothing }



-- | Runs a check on the head of a list. This check forces the list ot have at
--   least one element.

forcedCheck :: (a -> Bool) -> [a] -> Property
forcedCheck prop xs = not (null xs) ==> prop (head xs)



-- | Runs a trivial check on a list. If the list is empty, the property is not
--   checked.

trivialCheck :: (a -> Bool) -> [a] -> Property
trivialCheck prop xs = 
  (`classify` "trivial") (null xs) (if null xs then True else prop (head xs))



-- | Runs a local check.

runLocalCheck :: [Declaration] -> [Declaration]
runLocalCheck = fst . runWriter . checkLocal



-- | Tests if an identifier is not equal to one of the primitive type names.

isNotPrimitive :: Identifier -> Bool
isNotPrimitive i =
  unpackIdent i `notElem` [ "Int", "Integer", "Float", "Double", "Char" ]



-- | Tests if a given element contains FixedTypeExpressions.

hasFixedTypeExpressions :: (Typeable a, Data a) => a -> Bool
hasFixedTypeExpressions =
  everything (||) (False `mkQ` (const True :: FixedTypeExpression -> Bool))



-- | Tests if an element is nested.

isNested :: (Typeable a, Data a) => Identifier -> a -> Bool
isNested con = everything (||) (False `mkQ` nested)
  where
    nested t = case t of
      TypeCon (Con c) ts -> (c == con) && (any (not . isTypeVar) ts)
      otherwise          -> False

    isTypeVar t = case t of
      TypeVar _ -> True
      otherwise -> False



-- | Tests if an element is recursive.

isRecursive :: (Typeable a, Data a) => Identifier -> a -> Bool
isRecursive con = everything (||) (False `mkQ` (\c -> c == con))



