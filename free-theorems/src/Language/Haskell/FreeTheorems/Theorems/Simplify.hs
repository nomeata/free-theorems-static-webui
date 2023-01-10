{-# OPTIONS_GHC -fglasgow-exts #-}

module Language.Haskell.FreeTheorems.Theorems.Simplify
	( simplify
        , simplifyUnfoldedLift
 	)
where

import Data.Generics
import Data.Generics.Aliases
import Data.Generics.Schemes
import Data.Generics.Text (gshow)

import Language.Haskell.FreeTheorems.Theorems

simplify :: Formula -> Formula
simplify f = gsimplify f

simplifyUnfoldedLift :: UnfoldedLift -> UnfoldedLift
simplifyUnfoldedLift l = gsimplify l


-- Generics stuff:

type ScopeInfo = [TermVariable]

gsimplify :: Data d => (d -> d)
gsimplify = everywhereScoped (\s -> id
				    `extT` simplifyTerm
                                    `extT` simplifyPredicate
                                    `extT` simplifyFormula s
			     ) []

everywhereScoped :: (ScopeInfo -> GenericT) -> ScopeInfo -> GenericT
everywhereScoped = everywhereContext gupdateScope

-- Remember variables in scope

gupdateScope :: (ScopeInfo -> GenericQ ScopeInfo)
gupdateScope s = s `mkQ` flip updateScopeFormula s

-- This will remember all variables currently in scope
updateScopeFormula :: Formula -> ScopeInfo -> ScopeInfo
updateScopeFormula (ForallFunctions (Left  tv) _ _ _) = (tv:)
updateScopeFormula (ForallFunctions (Right tv) _ _ _) = (tv:)
updateScopeFormula (ForallVariables tv _ _)           = (tv:)
updateScopeFormula _                                  = id


-- Simplificatoins

simplifyFormula :: ScopeInfo -> Formula -> Formula

-- Remove unused quantified variables
simplifyFormula	_ (ForallVariables tv _ f) | not (tv `occursIn` f) = f
 
-- ∀v.f v == g v ⇒ f == g
simplifyFormula	_ (ForallVariables tv _ (Predicate (t1 `IsEqual` t2)))
                                           | Just (f1,v1) <- toFunApp t1
                                           , Just (f2,v2) <- toFunApp t2
                                           , v1 == v2
				           , (TermVar tv) == v1
                                           = gsimplify $ Predicate (f1 `IsEqual` f2)
 
-- Find definitions, and apply as far as possible
simplifyFormula s (ForallVariables tv t f) | [def] <- possibleDefs tv f
		  	                   = gsimplify $ -- Will loop if the definition
                                                         -- would not remove itself
					        ForallVariables tv t
                                                (replaceTerm s (TermVar tv) def f)
-- Remove empty Implication
simplifyFormula _ (Implication (Predicate IsTrue) f) 
                                           = f

-- Nothing to optimize
simplifyFormula _ f                        = f

simplifyPredicate :: Predicate -> Predicate

-- Remove tautologies
simplifyPredicate (IsEqual t1 t2) | t1 == t2
                                  = IsTrue

{- This is wrong: The variable might be constrained:

-- Eta reduction on both sides of an equality
simplifyPredicate (IsEqual t1 t2) | Just (f1,v1) <- toFunApp t1
                                  , Just (f2,v2) <- toFunApp t2
                                  , v1 == v2
                                  = gsimplify (IsEqual f1 f2) -- run simplification again
-}

-- Nothing to optimize
simplifyPredicate p               = p


simplifyTerm :: Term -> Term

-- Simplify function concatenations
simplifyTerm (TermComp [f]) = f
simplifyTerm (TermComp (f : (TermComp fs) : r))
                            = gsimplify (TermComp (f:fs ++ r))

-- Nothing to optimize
simplifyTerm t                = t
	

-- Actions

replaceTerm :: ScopeInfo -> Term -> Term -> GenericT
replaceTerm s0 t def = everywhereScoped (\s -> mkT (repl s)) s0
  where repl :: ScopeInfo -> Term -> Term
        repl s term | term == t
                    , null (listify (not . (`elem` s)) def)
                    = def
                    | otherwise
                    = term

-- Inspections

toFunApp :: Term -> Maybe (Term, Term)
toFunApp (TermApp f v) | Just (fs,v') <- toFunApp v
                       = Just (TermComp [f,fs],v')
toFunApp (TermApp f v) = Just (f,v)
toFunApp _             = Nothing

occursIn :: (Typeable a, Data a1, Eq a) => a -> a1 -> Bool
e `occursIn` e' = gAny (==e) e'

possibleDefs :: TermVariable -> GenericQ [Term]
possibleDefs tv a = everything (.) (id `mkQ` test) a []
  where test (t1 `IsEqual` t2) | t1 == (TermVar tv) = (t2:)
                               | t2 == (TermVar tv) = (t1:)
        test _                 =  id

-- Generic functions

gAny :: Typeable b => (b -> Bool) -> GenericQ Bool
gAny p = everything (||) (False `mkQ` p)

-- | Extend version of 'everywhere', which keeps information about the context around
everywhereContext :: (ctx -> GenericQ ctx) -> 
	             (ctx -> GenericT) ->
                      ctx ->
		      GenericT
everywhereContext ctxUpdate f ctx d
	= let ctx' = ctxUpdate ctx d
          in f ctx (gmapT (everywhereContext ctxUpdate f ctx') d)


