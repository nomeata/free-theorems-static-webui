


-- | Defines functions which help to define tests.

module Tests (
    module Arbitraries
  , doTest
) where



import Test.QuickCheck

import Arbitraries



-- | Runs a test in a standardised way.
--   
--   A test must have a label which should not be longer than 75 characters.
--   Otherwise, it is truncated.

doTest :: (Arbitrary a, Show a, Testable b) => String -> (a -> b) -> IO ()
doTest name prop = do
  putStrLn (fixString 75 name ++ ":")
  putStr "   "
  quickCheckWith (stdArgs {maxSuccess = 100}) prop   -- quickCheck prop
  where
    fixString :: Int -> String -> String
    fixString len s =
      if length s <= len
        then s
        else take (len - 3) s ++ "..."




