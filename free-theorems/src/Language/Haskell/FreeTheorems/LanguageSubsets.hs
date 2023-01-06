{-# LANGUAGE DeriveDataTypeable #-}

-- | Declares the available Haskell language subsets and the result types for
--   generating free theorems. 

module Language.Haskell.FreeTheorems.LanguageSubsets where



import Data.Generics (Typeable, Data)



-- | Descriptions of the Haskell language subsets for which free theorems can
--   be generated.

data LanguageSubset
  = BasicSubset
        -- ^ This subset describes only terms in which no undefinedness may.
        --   This excludes terms defined using general recursion or selective
        --   strictness (as offered by @seq@).

  | SubsetWithFix TheoremType
        -- ^ This subset describes terms in which undefined values may occur
        --   such as introduced by a fixpoint combinator or possibly failing
        --   pattern matches (if not all cases are covered).
        --   This excludes any term based on @seq@.

  | SubsetWithSeq TheoremType
        -- ^ Additionally to the fix subset, this subset allows terms to
        --   be defined using @seq@.

  deriving (Typeable, Data, Eq)



-- | Returns the theorem type for a given language subset.

theoremType :: LanguageSubset -> TheoremType
theoremType l = case l of
  BasicSubset     -> EquationalTheorem
  SubsetWithFix t -> t
  SubsetWithSeq t -> t



-- | The result type for generating free theorems.

data TheoremType
  = EquationalTheorem
        -- ^ An equational free theorem should be generated.

  | InequationalTheorem
        -- ^ Two inequational free theorems should be generated.

  deriving (Typeable, Data, Eq)



