


-- | Defines functions to ensure that only valid declarations and type 
--   signatures are fed to the FreeTheorems library. The given functions are
--   intended as second stage after parsing declarations.

module Language.Haskell.FreeTheorems.Frontend (
    Checked
  , Parsed
  , runChecks
  , check
  , checkAgainst
) where



import Data.Generics (everything, extQ, mkQ)
import Data.List (partition, intersect)
import Data.Maybe (mapMaybe)

import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.ValidSyntax (ValidDeclaration (..))
import Language.Haskell.FreeTheorems.Frontend.Error (Checked, Parsed, runChecks)
import Language.Haskell.FreeTheorems.Frontend.TypeExpressions
    (replaceAllTypeSynonyms, closeTypeExpressions)
import Language.Haskell.FreeTheorems.Frontend.CheckLocal
    (checkLocal, checkDataAndNewtypeDeclarations)
import Language.Haskell.FreeTheorems.Frontend.CheckGlobal (checkGlobal)



-- | Checks a list of declarations.
--   It returns a list of all declarations which are valid and an error message
--   for all those declarations which are not valid.

check :: [Declaration] -> Checked [ValidDeclaration]
check = checkAgainst []



-- | Checks a list of declarations against a given list of valid
--   declarations.
--   It returns a list of all declarations from the second argument which are
--   valid. Moreover, the result contains an error message for all those
--   declarations which are not valid.
--
--   The declarations given in the second argument may be based on those of the
--   first argument. For example, if the first argument contains a valid
--   declaration of a type \"Foo\" and if the second argument contains the
--   following declaration
--
--   > type Bar = Foo
--
--   then also the declaration of \"Bar\" is valid.

checkAgainst :: 
    [ValidDeclaration] 
    -> [Declaration] 
    -> Checked [ValidDeclaration]

checkAgainst vds ds = 
    
    -- start from 'ds'
  return ds
   
    -- perform local checks:
    --   * free variables of the right-hand side are declared on the left-hand
    --     of declarations
    --   * type variables of the left-hand side are pairwise distinct
    --   * primitive types are not declared
    --   * FixedTypeExpression does not occur anywhere
    --   * type synonyms are not recursive
    --   * data and newtype are not nested
    --   * classes methods are pairwise distinct, don't use the owning class
    --     and have the class variable as free variable
  >>= checkLocal
  
    -- perform global checks:
    --   * at most one declaration per name
    --   * arity checks of type constructors in all type expressions
    --   * type class hierarchy is acyclic
    --   * type synonym declarations are not mutually recursive
    --   * all used constructors and classes are declared
  >>= checkGlobal vds

    -- replace all type synonyms, use also the valid type synonyms
  >>= \ds' -> 
    let getTypeSyn d = case d of { TypeDecl t -> Just t ; otherwise -> Nothing }
        typeSyns = mapMaybe getTypeSyn (map rawDeclaration vds ++ ds')
     in return (replaceAllTypeSynonyms typeSyns ds')

    -- checks in data and newtype declarations: no abstractions, no functions
  >>= checkDataAndNewtypeDeclarations

    -- finally, close all type signatures and class methods and transform all
    -- declarations to valid ones
  >>= return . makeValid vds . closeTypeExpressions



-- | Turns a list of declarations into valid declarations.
--   Additionally, every declaration is checked whether it depends on any 
--   algebraic data type with strictness flags.

makeValid :: [ValidDeclaration] -> [Declaration] -> [ValidDeclaration]
makeValid vds ds = 
  let strict = map rawDeclaration (filter isStrictDeclaration vds)
      knownStrict = map getDeclarationName 
                        (strict ++ filter hasStrictnessFlags ds)
      
      rec ss ds = 
        let (ns, os) = partition (dependsOnStrictTypes ss) ds
         in if null ns
              then ss
              else rec (ss ++ map getDeclarationName ns) os

      allStrict = rec knownStrict ds
   
   in map (\d -> ValidDeclaration d (getDeclarationName d `elem` allStrict)) ds
  where
    hasStrictnessFlags d = 
      let hasBang (Banged _)   = True
          hasBang (Unbanged _) = False
       in everything (||) (False `mkQ` hasBang) d
    
    dependsOnStrictTypes ss d = 
      let getCons c = case c of { Con n -> [n] ; otherwise -> [] }
          getClasses (TC n) = [n]
          ns = everything (++) ([] `mkQ` getCons `extQ` getClasses) d
       in not (null (ns `intersect` ss))

 



