


module FrontendTypeExpressionsTests (tests) where



import Data.Generics (everything, something, somewhere, mkQ, gcount, mkM)
import Data.Map as Map (elems, keysSet, singleton, insert, fromList)
import Data.Set as Set
    ( isSubsetOf, union, member, null, intersection, fromList, difference
    , empty, size, singleton )

import Tests
import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.Frontend.TypeExpressions



-- | Runs all tests.

tests :: IO ()
tests = do
  doTest "freeVariables are in allVariables" prop_freeVariablesAllVariables
  doTest "every variable is free or bound" prop_freeVariablesBoundVariables
  doTest "allVariables finds at least one variable of a type "
    prop_variablesAreFound
  doTest "closure binds free variables" prop_closureVariables
  doTest "freeVariables . closure == []" prop_closureFreeVariables
  doTest "closureFor emptySet == id" prop_closureForEmptySet
  doTest "count after closure is correct" prop_closureCount
  doTest "createNewTypeVariable creates unique variables"
    prop_createNewTypeVariableNotIn
  doTest"count after alphaConversion is correct" prop_alphaConversionCount
  doTest "alphaConversion keeps freeVariables" prop_alphaConversionFreeVariables
  doTest "alphaConversion substitutes a variable" prop_alphaConversionVariable
  doTest "substituteVariable replaces free variable"
    prop_substituteTypeVariableReplacesFreeVariables
  doTest "substituteVariable keeps free variables"
    prop_substituteTypeVariableKeepsFreeVariables
  doTest "type is contained after substituteTypeVariables"
    prop_substituteTypeVariableTypeInserted
  doTest "count after substituteVariable is correct"
    prop_substituteTypeVariableWithCount





------- Test properties -------------------------------------------------------


-- | Property: Free variables of a type expression are a subset of all
--   type variables occurring in a type expression.

prop_freeVariablesAllVariables t = 
  freeTypeVariables t `Set.isSubsetOf` allTypeVariables t
  where types = t :: TypeExpression



-- | Property: Every type variable occurring in a type expression is free or
--   bound.

prop_freeVariablesBoundVariables t = (free `Set.union` bound) == all
  where 
    types = t :: TypeExpression
    free  = freeTypeVariables t
    all   = allTypeVariables  t
    bound = boundVariables t



-- | Property: If a type expression contains at least one variable, it is also
--   found by allTypeVariables.

prop_variablesAreFound t =
  maybe True (\v -> v `Set.member` allTypeVariables t) (getVariableFrom t)
  where 
    types = t :: TypeExpression



-- | Property: Given a set of type variables, the closure of a type expression
--   for this set does not contain free type variables in that set.

prop_closureVariables t vs =
  Set.null (set `Set.intersection` freeTypeVariables (closureFor set t))
  where
    types = (t :: TypeExpression, vs :: [TypeVariable])
    set = Set.fromList vs



-- | Property: There are no free type variables after closing a type expression
--   for all free type variables.

prop_closureFreeVariables t =
  Set.null . freeTypeVariables . closureFor (freeTypeVariables t) $ t
  where
    types = t :: TypeExpression



-- | Property: The closure for an empty set of type variables does not change a
--   type expression.

prop_closureForEmptySet t = closureFor Set.empty t == t
  where
    types = t :: TypeExpression
  


-- | Property: The count of type constructors does not increase by the closure.

prop_closureCount t vs = 
  countTypeAbs t + Set.size set == countTypeAbs (closureFor set t)
  && countTypeFun t == countTypeFun (closureFor set t)
  && countTypeCon t == countTypeCon (closureFor set t)
  where
    types = (t :: TypeExpression, vs :: [TypeVariable])
    set = Set.fromList vs



-- | Property: A newly created type variable does not occur in the list of
--   forbidden type variables.

prop_createNewTypeVariableNotIn vs =
  not (createNewTypeVariableNotIn s `Set.member` s)
  where
    types = vs :: [TypeVariable]
    s = Set.fromList vs



-- | Property: Alpha conversion does not increase or decrease the number of
--   type constructors.

prop_alphaConversionCount t v =
  countTypeCon t == countTypeCon (alphaConversion v t)
  && countTypeAbs t == countTypeAbs (alphaConversion v t)
  && countTypeFun t == countTypeFun (alphaConversion v t)
  where types = (t :: TypeExpression, v :: TypeVariable)



-- | Property: Alpha conversion keeps free variables free.

prop_alphaConversionFreeVariables t v =
  freeTypeVariables t == freeTypeVariables (alphaConversion v t)
  where types = (t :: TypeExpression, v :: TypeVariable)



-- | Property: After alpha conversion, the replaced variable does not occur
--   in the type expression (except as free variable) and is not bound anymore.

prop_alphaConversionVariable t v =
  (v `Set.member` freeAfterAC || not (v `Set.member` allAfterAC))
  && not (v `Set.member` boundVariables acT)
  where
    types = (t :: TypeExpression, v :: TypeVariable)
    acT = alphaConversion v t
    allAfterAC  = allTypeVariables acT
    freeAfterAC = freeTypeVariables acT



-- | Property: Replacing type variables with (closed) type expressions in a
--   type expression removes the free variables from the latter type
--   expression (as long as they are not free in any type expression which is
--   inserted).

prop_substituteTypeVariableReplacesFreeVariables (v1,v2) (t1,t2) t =
  (not (v1 `Set.member` vs)
   || v1 `Set.member` freeTypeVariables (fooCon (Map.elems m))
   || not (v1 `Set.member` freeTypeVariables rt))
  &&
  (not (v2 `Set.member` vs)
   || v2 `Set.member` freeTypeVariables  (fooCon (Map.elems m))
   || not (v2 `Set.member` freeTypeVariables rt))

  where
    types = (v1 :: TypeVariable, v2 :: TypeVariable,
             t1 :: TypeExpression, t2 :: TypeExpression,
             t :: TypeExpression)
    m  = Map.fromList [(v1,t1), (v2,t2)]
    vs = Map.keysSet m
    rt = substituteTypeVariables m t
    fooCon = TypeCon (Con $ Ident "Foo")
    


-- | Property: Replacing a type variable in a type expression keeps the other
--   free variables free.

prop_substituteTypeVariableKeepsFreeVariables (v1,v2) (t1,t2) t i =
  (freeT `Set.difference` vs) `Set.isSubsetOf` freeR
  where
    types = (v1 :: TypeVariable, v2 :: TypeVariable,
             t1 :: TypeExpression, t2 :: TypeExpression, 
             t :: TypeExpression, i :: Int)
    m1 = Map.singleton v1 t1
    m  = if i `mod` 2 == 0 then m1 else Map.insert v2 t2 m1
    vs = Map.keysSet m
    rt = substituteTypeVariables m t
    freeT = freeTypeVariables t
    freeR = freeTypeVariables rt



-- | Property: If a type variable which should be substituted by a type
--   expression is free, then the type expression must occur in the result.

prop_substituteTypeVariableTypeInserted (v1,v2) (t1,t2) t =
  (not (v1 `Set.member` freeTypeVariables t) || t1 `occursIn` rt)
  &&
  (not (v2 `Set.member` freeTypeVariables t) || t2 `occursIn` rt)
  where
    types = (v1 :: TypeVariable, v2 :: TypeVariable,
             t1 :: TypeExpression, t2 :: TypeExpression,
             t :: TypeExpression)
    m  = Map.fromList [(v1,t1), (v2,t2)]
    vs = Map.keysSet m
    rt = substituteTypeVariables m t



-- | Property: Replacing a type variable increases only the number of type
--   constructors.

prop_substituteTypeVariableWithCount (v1,v2) (t1,t2) t i =
  countTypeFun rt >= countTypeFun t
  && countTypeAbs rt >= countTypeAbs t
  && countTypeCon rt >= countTypeCon t
  where
    types = (v1 :: TypeVariable, v2 :: TypeVariable,
             t1 :: TypeExpression, t2 :: TypeExpression, 
             t :: TypeExpression, i :: Int)
    m1 = Map.singleton v1 t1
    m  = if i `mod` 2 == 0 then m1 else Map.insert v2 t2 m1
    vs = Map.keysSet m
    rt = substituteTypeVariables m t





-- Test helper functions ------------------------------------------------------



-- | Returns a set of all bound variables of a type expression.

boundVariables t = everything Set.union (Set.empty `mkQ` select) t
  where
    select t = case t of
      TypeAbs v _ _ -> Set.singleton v 
      otherwise     -> Set.empty



-- | Returns the first variable found in a type expression.
getVariableFrom t = something (Nothing `mkQ` select) t
  where
    select t = case t of
      TypeVar v     -> Just v
      TypeAbs v _ _ -> Just v
      otherwise     -> Nothing



-- | Counts the number of user-defined type constructors.

countTypeCon t = gcount (False `mkQ` select) t
  where
    select t = case t of
      TypeCon _ _ -> True
      otherwise   -> False



-- | Counts the number of function type constructors.

countTypeFun t = gcount (False `mkQ` select) t
  where
    select t = case t of
      TypeFun _ _ -> True
      otherwise   -> False



-- | Counts the number of type abstraction constructors. 

countTypeAbs t = gcount (False `mkQ` select) t
  where
    select t = case t of
      TypeAbs _ _ _ -> True
      otherwise     -> False



-- | Returns True if t1 occurs in t2.

t1 `occursIn` t2 = case somewhere (mkM $ findT t2) t1 of
  Nothing -> False
  Just _  -> True
  where
    findT t1 t2 = if (t1 == t2) then Just t1 else Nothing




