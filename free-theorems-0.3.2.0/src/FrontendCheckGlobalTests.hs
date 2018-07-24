


module FrontendCheckGlobalTests (tests) where



import Control.Monad.Writer (runWriter)
import Data.Generics (everything, mkQ)
import Data.List (nub, find)
import Data.Maybe (mapMaybe, catMaybes)
import Data.Set as Set (isSubsetOf, union, empty, singleton, fromList)
import Test.QuickCheck

import Tests
import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.Frontend as FT 
import Language.Haskell.FreeTheorems.Frontend.CheckGlobal




-- | Runs all tests.

tests :: IO ()
tests = do
  doTest "check global at most one declaration per name"
    prop_checkGlobalAtMostOneDeclPerName
  doTest "check global arities match" prop_checkGlobalAritiesMatch
  doTest "check global type class hierarchy acyclic"
    prop_checkGlobalAcyclicTypeClasses
  doTest "check global type synonyms not mutually recursive"
    prop_checkGlobalTypeSynonymsNotMutuallyRecursive
  doTest "check global only declared classes occur"
    prop_checkGlobalTypeClasses    
  doTest "check global only declared constructors occur"
    prop_checkGlobalConstructors





-- | Property: Check that there are no duplicate declarations by comparing the 
--   names of the declarations.

prop_checkGlobalAtMostOneDeclPerName ds0 =
  checkDecls ds0 $ \ds ->
    let names = map getDeclarationName ds
     in length (nub names) == length names



-- | Property: Checks that every type constructor is used with the arity it was
--   declared with. If any occurring type constructor is not declared, no arity
--   check is performed for it.

prop_checkGlobalAritiesMatch ds0 =
  checkDecls ds0 $ \ds ->
    everything (&&) (True `mkQ` checkArity ds) ds
    
checkArity ds t = case t of
  TypeCon con ts -> correctArity ds con (length ts)
  otherwise      -> True

correctArity ds con arity = case con of
  ConUnit    -> arity == 0
  ConList    -> arity == 1
  ConTuple n -> arity == n
  ConInt     -> arity == 0
  ConInteger -> arity == 0
  ConFloat   -> arity == 0
  ConDouble  -> arity == 0
  ConChar    -> arity == 0
  Con c      -> maybe True (== arity) (getArityFromDecl ds c)

getArityFromDecl ds c =
  case find (\d -> getDeclarationName d == c) ds of
    Just (DataDecl d)    -> Just . length . dataVars $ d
    Just (NewtypeDecl d) -> Just . length . newtypeVars $ d
    Just (TypeDecl d)    -> Just . length . typeVars $ d
    otherwise            -> Nothing



-- | Property: Checks that the type class hierarchy is acyclic.

prop_checkGlobalAcyclicTypeClasses ds0 =
  checkDecls ds0 $ \ds ->
    hasCycle classDeps ds

classDeps d = case d of
  ClassDecl d -> map (\(TC c) -> c) (superClasses d)
  otherwise   -> []



-- | Property: Checks that type synonyms are not mutually recursively declared.

prop_checkGlobalTypeSynonymsNotMutuallyRecursive ds0 =
  checkDecls ds0 $ \ds ->
    hasCycle (typeDeps (mapMaybe getTypeSynName ds)) ds

getTypeSynName d = case d of
  TypeDecl d -> Just (typeName d)
  otherwise  -> Nothing

typeDeps ds = everything (++) ([] `mkQ` getTypeCon)
  where
    getTypeCon t = case t of
      TypeCon (Con c) _ -> if c `elem` ds then [c] else []
      otherwise         -> []



-- | Property: Check that every occurring type class is declared.

prop_checkGlobalTypeClasses ds0 =
  checkDecls ds0 $ \ds ->
    occurringClasses ds `Set.isSubsetOf` declaredClasses ds
  
occurringClasses = everything Set.union (Set.empty `mkQ` occurring)
  where
    occurring (TC c) = Set.singleton c

declaredClasses = Set.fromList . mapMaybe getClassName
  where
    getClassName d = case d of
      ClassDecl d -> Just (className d)
      otherwise   -> Nothing



-- | Property: Check that every occurring type constructor is declared.

prop_checkGlobalConstructors ds0 =
  checkDecls ds0 $ \ds ->
    occurringCons ds `Set.isSubsetOf` declaredCons ds

occurringCons = everything Set.union (Set.empty `mkQ` occurring)
  where
    occurring con = case con of
      Con c     -> Set.singleton c
      otherwise -> Set.empty

declaredCons = Set.fromList . mapMaybe getConName
  where
    getConName d = case d of
      DataDecl d    -> Just (dataName d)
      NewtypeDecl d -> Just (newtypeName d)
      TypeDecl d    -> Just (typeName d)
      otherwise     -> Nothing







-- | Runs a property on to list of declarations. The first list is checked
--   and then fed to 'checkGlobal' along with the second list. The result
--   and the first (checked) list are then given to the property.

checkDecls :: ListOfDeclarations -> ([Declaration] -> Bool) -> Property
checkDecls ds prop =
  let ds' = fst . runWriter . checkGlobal [] . getDeclarations $ ds
   in not (null ds') ==> prop ds'
        


-- | Checks if the given list of declarations has any cycles. The test is based
--   on the provided function which computes the dependencies of a declaration.

hasCycle :: (Declaration -> [Identifier]) -> [Declaration] -> Bool
hasCycle deps ds = 
  any (\d -> cycle (length ds) d d) ds
  where
    cycle i d1 d2 =
      if i == 0
        then False
        else null (deps d2)
             || getDeclarationName d1 `elem` deps d2
             || any (cycle (i-1) d1) (declsDependingOn d2)

    declsDependingOn d =
      filter (\d' -> getDeclarationName d' `elem` deps d) ds



