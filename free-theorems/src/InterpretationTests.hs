



module InterpretationTests (tests) where



tests :: IO ()
tests = do
  return ()




{-
-- Helper functions -----------------------------------------------------------



-- | Counts the number of relational actions of the function type constructor.

countRelFun t = gcount (False `mkQ` select) t
  where
    select t = case t of
      RelFun _ _ _ -> True
      otherwise    -> False



-- | Counts the number of relational actions of the type abstraction
--   constructor.

countRelAbs t = gcount (False `mkQ` select) t
  where
    select t = case t of
      RelAbs _ _ _ -> True
      otherwise    -> False



-- | Counts the number of relational actions of nullary type constructors.

countRelBasic t = gcount (False `mkQ` select) t
  where
    select t = case t of
      RelBasic _   -> True
      otherwise -> False



-- | Counts the number of relational actions for n-ary type constructors.

countRelLift t = gcount (False `mkQ` select) t
  where
    select t = case t of
      RelLift _ _ -> True
      otherwise   -> False



-- Define the test properties -------------------------------------------------



-- | Property: The number of type constructors must equal the number of
--   corresponding relations.

prop_interpretCount t l =
  countTypeFun t' == countRelFun rel
  && countTypeAbs t' == countRelAbs rel
  && countTypeCon t' == countRelLift rel + countRelBasic rel
  where
    types = (t :: TypeExpression, l :: LanguageSubset)
    t' = closure t
    sig = ValidSignature (Signature (Ident "x") t')
    Intermediate _ rel = interpret l sig



-- Run the tests --------------------------------------------------------------



-- | The main function which runs the list of tests.

main = do
  t "count after interpretation is ok                   "
    prop_interpretCount

  where
    t desc prop = do
      putStr $ desc ++ " ... "
      -- quickCheck prop
      check (defaultConfig {configMaxTest = 100}) prop

-}



