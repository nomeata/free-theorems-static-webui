

module FrontendOtherTests (tests) where



import Control.Monad (liftM)
import Control.Monad.Writer (runWriter)
import Data.Generics (gcount, mkQ)
import Data.Maybe (mapMaybe)
import Data.Set as Set (isSubsetOf)
import Test.QuickCheck 

import Tests

import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.ValidSyntax
import Language.Haskell.FreeTheorems.Frontend as FT
import Language.Haskell.FreeTheorems.Frontend.TypeExpressions
import Language.Haskell.FreeTheorems.Frontend.CheckLocal
import Language.Haskell.FreeTheorems.Frontend.CheckGlobal



-- | Runs all tests.

tests :: IO ()
tests = do
  doTest "replaceTypeSynonyms is complete" prop_replaceTypeSynonymsIsComplete
  doTest "check is stable" prop_checkIsStable






-- | Property: Replacing every type synonym in a type expression does not leave
--   any type synonym.

prop_replaceTypeSynonymsIsComplete ds = 
  withTypeDecls ds $ \ts ->
    let ds' = getDeclarations ds
    in countTypeConSyn ts (replaceAllTypeSynonyms ts ds') == 0

countTypeConSyn ts = gcount (False `mkQ` select)
  where 
    select con = case con of
      Con c     -> c `elem` map typeName ts
      otherwise -> False



-- | Checks a list of declarations and filters all type declarations which then
--   are fed to a property.

withTypeDecls :: ListOfDeclarations -> ([TypeDeclaration] -> Bool) -> Property
withTypeDecls ds prop =
  let getTypeSyn d = case d of { TypeDecl d -> Just d ; otherwise -> Nothing }
      process ds = fst . runWriter $ checkLocal ds >>= checkGlobal []
      typeSyns = mapMaybe getTypeSyn . process . getDeclarations $ ds
   in (`classify` "trivial") (null typeSyns) $ prop typeSyns




-- | Property: Checks that applying 'check' twice does not more that applying
--   'check once.

prop_checkIsStable ds = 
  let once  ds = FT.check ds
      twice ds = FT.check . map rawDeclaration =<< FT.check ds
      count f = length . fst . runWriter . f . getDeclarations $ ds
   in count once == count twice 




