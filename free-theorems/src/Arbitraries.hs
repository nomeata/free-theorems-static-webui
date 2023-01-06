


-- | Gives instance of the class Arbitrary for several data types of the
--   library. These instances are needed by QuickCheck.
--   See also "Tests".

module Arbitraries where



import Control.Monad
import Data.Generics (Typeable, Data)
import Test.QuickCheck

import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.LanguageSubsets



newtype ListOfDeclarations = ListOfDeclarations 
  { getDeclarations :: [Declaration] }
  deriving (Eq, Show)

instance Arbitrary ListOfDeclarations where
  arbitrary = do n <- choose (1, 100)
                 liftM ListOfDeclarations (replicateM n arbitrary)

instance CoArbitrary ListOfDeclarations where
  coarbitrary _ = id



instance Arbitrary Declaration where
  arbitrary = oneof [ liftM DataDecl arbitrary
                    , liftM NewtypeDecl arbitrary
                    , liftM TypeDecl arbitrary
                    , liftM ClassDecl arbitrary
                    , liftM TypeSig arbitrary ]

instance CoArbitrary Declaration where
  coarbitrary _ = id



instance Arbitrary DataDeclaration where
  arbitrary = do n <- arbIdent id 'T'
                        [ "Bool", "Maybe", "Either", "Ordering" ]
                 v <- choose (0, 5)
                 c <- choose (1, 7)
                 liftM2 (Data n) (replicateM v arbitrary) 
                                 (replicateM c arbitrary)

instance CoArbitrary DataDeclaration where
  coarbitrary _ = id



instance Arbitrary NewtypeDeclaration where
  arbitrary = do n <- arbIdent id 'T' []
                 v <- choose (0, 5)
                 c <- arbIdent id 'D' []
                 liftM2 (\vs -> Newtype n vs c)
                        (replicateM v arbitrary) arbitrary

instance CoArbitrary NewtypeDeclaration where
  coarbitrary _ = id



instance Arbitrary TypeDeclaration where
  arbitrary = do n <- arbIdent id 'T'
                        [ "String", "Ordering", "Rational", "ShowS", "ReadS"
                        , "FilePath" ]
                 v <- choose (0, 5)
                 liftM2 (Type n) (replicateM v arbitrary) arbitrary

instance CoArbitrary TypeDeclaration where
  coarbitrary _ = id



instance Arbitrary ClassDeclaration where
  arbitrary = do c <- choose (0, 3)
                 p <- replicateM c (arbitrary :: Gen TypeClass)
                 n <- arbIdent id 'C'
                        [ "Eq", "Ord", "Num", "Integral", "Show", "Read"
                        , "Bounded", "Enum", "Real", "Fractional", "Floating"
                        , "RealFrac", "RealFloat" ]
                 s <- choose (0, 10)
                 liftM2 (Class p n) arbitrary (replicateM s arbitrary)

instance CoArbitrary ClassDeclaration where
  coarbitrary _ = id



instance Arbitrary Signature where
  arbitrary = do s <- arbIdent id 'f'
                        [ "not", "(&&)", "(||)", "(==)", "(/=)", "maybe"
                        , "either", "fst", "snd", "curry", "uncurry", "(<)"
                        , "(>)", "max", "min", "succ", "pred", "(+)", "(-)"
                        , "div", "mod", "pi", "id", "flip", "const", "map"
                        , "filter", "head", "tail", "length", "foldr", "foldl" ]
                 liftM (Signature s) arbitrary

instance CoArbitrary Signature where
  coarbitrary _ = id



instance Arbitrary DataConstructorDeclaration where
  arbitrary = do con <- arbIdent id 'D'
                            [ "False", "True", "Left", "Right", "Nothing"
                            , "Just", "LT", "GT", "EQ" ]
                 i <- choose (0, 5)
                 liftM (DataCon con) (replicateM i arbitrary)

instance CoArbitrary DataConstructorDeclaration where
  coarbitrary _ = id



instance Arbitrary BangTypeExpression where
  arbitrary = oneof [ liftM Banged arbitrary, liftM Unbanged arbitrary ]

instance CoArbitrary BangTypeExpression where
  coarbitrary _ = id



instance Arbitrary TypeExpression where
  arbitrary = sized arbTypeExpr

instance CoArbitrary TypeExpression where
  coarbitrary _ = id

arbTypeExpr n =
  if n == 0
    then oneof [ liftM TypeVar arbitrary
               , liftM (\c -> TypeCon c []) arbitrary
               , liftM TypeExp arbitrary ]
    else frequency [ (1, arbTypeExpr 0)
                   , (2, arbComplexTypeExpr (n `div` 2))
                   ]

arbComplexTypeExpr n = oneof
  [ do r <- choose (1, 7)
       liftM2 TypeCon arbitrary (replicateM r (arbTypeExpr n))
  , liftM2 TypeFun (arbTypeExpr n) (arbTypeExpr n)
  , do c <- choose (0, 2)
       liftM3 TypeAbs arbitrary (replicateM c arbitrary) (arbTypeExpr n)
  ]



instance Arbitrary TypeConstructor where
  arbitrary = oneof
                [ oneof 
                    [ return ConUnit
                    , return ConList
                    , do n <- choose (2, 15)
                         return (ConTuple n)
                    , return ConInt
                    , return ConInteger
                    , return ConFloat
                    , return ConDouble
                    , return ConChar
                    ]
                , arbIdent Con 'T' 
                    [ "Bool", "Maybe", "Either", "String", "Ordering"
                    , "Rational", "ShowS", "ReadS", "FilePath" ]
                ]

instance CoArbitrary TypeConstructor where
  coarbitrary _ = id



instance Arbitrary TypeVariable where
  arbitrary = arbIdent TV 'a' ["a", "b", "c", "d", "e"]

instance CoArbitrary TypeVariable where
  coarbitrary _ = id



instance Arbitrary TypeClass where
  arbitrary = arbIdent TC 'C'
                [ "Eq", "Ord", "Num", "Integral", "Show", "Read", "Bounded"
                , "Enum", "Real", "Fractional", "Floating", "RealFrac"
                , "RealFloat" ]

instance CoArbitrary TypeClass where
  coarbitrary _ = id



instance Arbitrary FixedTypeExpression where
  arbitrary = oneof (map (return . TF . Ident) [ "t1", "t2", "t3", "t4", "t5" ])


instance CoArbitrary FixedTypeExpression where
  coarbitrary _ = id



instance Arbitrary LanguageSubset where
  arbitrary = oneof
    [ return $ BasicSubset
    , return $ SubsetWithFix EquationalTheorem
    , return $ SubsetWithFix InequationalTheorem
    , return $ SubsetWithSeq EquationalTheorem
    , return $ SubsetWithSeq InequationalTheorem
    ]

instance CoArbitrary LanguageSubset where
  coarbitrary _ = id



arbIdent :: (Identifier -> a) -> Char -> [String] -> Gen a
arbIdent f c xs =
  oneof . map (return . f . Ident) $ xs ++ map (\i -> c : show i) [1..20]


