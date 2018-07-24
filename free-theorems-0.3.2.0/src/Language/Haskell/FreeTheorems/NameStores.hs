


-- | Provides functions to generate new variable names of different kinds.

module Language.Haskell.FreeTheorems.NameStores
    ( typeNameStore
    , relationNameStore
    , typeExpressionNameStore
    , functionNameStore1
    , functionNameStore2
    , variableNameStore
    ) where



import Data.List (unfoldr)



-- | An infinite list of names for type variables.

typeNameStore :: [String]
typeNameStore = createNames "abcde" 'a'



-- | An infinite list of names for relation variables.

relationNameStore :: [String]
relationNameStore = createNames "RS" 'R'



-- | An infinite list of names for type expressions.

typeExpressionNameStore :: [String]
typeExpressionNameStore = createNames "" 't'



-- | An infinite list of names for function variables.

functionNameStore1 :: [String]
functionNameStore1 = createNames "fgh" 'f'


-- | Another infinite list of names for function variables.

functionNameStore2 :: [String]
functionNameStore2 = createNames "pqrs" 'p'



-- | An infinite list of names for term variables.

variableNameStore :: [String]
variableNameStore = createNames "xyzvwabcdeijklmn" 'x'



-- | Creates an infinite list of names based on a list of simple names and a
--   default prefix. After simple names have been used, the numbers starting
--   from 1 are appended to the default prefix to generate more names.

createNames :: [Char] -> Char -> [String]
createNames prefixes prefix =
  let unpack is = case is of { (c:cs) -> Just ([c], cs) ; otherwise -> Nothing }
   in unfoldr unpack prefixes ++ (map (\i -> prefix : show i) [1..])



