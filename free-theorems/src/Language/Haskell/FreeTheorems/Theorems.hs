{-# LANGUAGE DeriveDataTypeable #-}


-- | Data structures to describe theorems generated from types.

module Language.Haskell.FreeTheorems.Theorems where



import Data.Generics (Typeable, Data)

import Language.Haskell.FreeTheorems.BasicSyntax
import Language.Haskell.FreeTheorems.LanguageSubsets



-- | A theorem which is generated from a type signature.

type Theorem = Formula



-- | Logical formula constituting automatically generated theorems.

data Formula 
  = ForallRelations RelationVariable (TypeExpression, TypeExpression)
                    [Restriction] Formula
        -- ^ Quantifies a relation variable and two type expressions.
  
  | ForallFunctions (Either TermVariable TermVariable) 
                    (TypeExpression, TypeExpression) [Restriction] Formula
        -- ^ Quantifies a function variable and two type expressions.
  
  | ForallPairs (TermVariable, TermVariable) Relation Formula
        -- ^ Quantifies two term variables taken from a relation.
  
  | ForallVariables TermVariable TypeExpression Formula
        -- ^ Quantifies a term variable of a certain type.
  
  | Equivalence Formula Formula
        -- ^ Two formulas are equivalent.
  
  | Implication Formula Formula
        -- ^ The first formula implies the second formula.
  
  | Conjunction Formula Formula
        -- ^ The first formula and the second formula.
  
  | Predicate Predicate
        -- ^ A basic formula.
  
  deriving (Typeable, Data)



-- | Restrictions on functions and relations.

data Restriction
  = Strict
  | Continuous
  | Total
  | BottomReflecting
  | LeftClosed
  | RespectsClasses [TypeClass]
  deriving (Typeable, Data, Eq)



-- | Predicates occurring in formulas.

data Predicate
  = IsMember Term Term Relation
        -- ^ The pair of two terms is contained in a relation.
  
  | IsEqual Term Term
        -- ^ Two terms are equal.
  
  | IsLessEq Term Term
        -- ^ The first term is less defined than the second one, based on the
        --   semantical approximation order.
  
  | IsNotBot Term
        -- ^ The term is not equal to @_|_@.

  | IsTrue
        -- ^ Constant True Predicate
  
  deriving (Typeable, Data)



-- | Terms consisting of variables, applications and instantiations.

data Term
  = TermVar TermVariable            -- ^ A term variable.
  | TermIns Term TypeExpression     -- ^ Instantiation of a term.
  | TermApp Term Term               -- ^ Application of a term to a term.
  | TermComp [Term]                 -- ^ Composition of function terms
  deriving (Typeable, Data, Eq)



-- | Variables occurring in terms.

newtype TermVariable = TVar String
  deriving (Typeable, Data, Eq)



-- | Relations are the foundations of free theorems.

data Relation
  = RelVar RelationInfo RelationVariable 
        -- ^ A relation variable.
 
  | FunVar RelationInfo (Either Term Term)
        -- ^ A function variable.
        --   It might be either a function to be applied on the left side (in
        --   equational and inequational cases) or on the right side (in 
        --   inequational cases only).
        --   In inequational cases, the term is additionally composed with the
        --   semantic approximation partial order.
 
  | RelBasic RelationInfo
        -- ^ A basic relation corresponding to a nullary type constructor.
        --   Depending on the theorem type, this can be either an equivalence
        --   relation or the semantic approximation partial order.
  
  | RelLift RelationInfo TypeConstructor [Relation]
        -- ^ A lifted relation for any nonnullary type constructor.
        --   The semantics of lifted relations is differs with the language
        --   subset:
        --   In inequational subsets lifted relations explicitly require
        --   left-closedness by composition with the semantic approximation 
        --   partial order.
        --   In equational subsets with fix or seq, this relation requires
        --   strictness explicitly by relating the undefined value with itself.
  
  | RelFun RelationInfo Relation Relation
        -- ^ A relation corresponding to a function type constructor.
        --   The semantics of this relation differs with the language subset:
        --   In the equational subset with seq, this relation is explicitly
        --   requiring bottom-reflectiveness of its members.
        --   In the inequational subset with seq, this relation is explicitly
        --   requiring totality of its members.

  | RelFunLab RelationInfo Relation Relation
        -- ^ A relation corresponding to a function type constructor.
        --   The semantics of this relation differs with the language subset:
        --   Apart from the equational subset with seq, it is equal to RelFun.
        --   In the equational subset with Seq, this relation is _not_ 
        --   explicitly requiring bottom-reflectiveness of its members.
  
  | RelAbs RelationInfo RelationVariable (TypeExpression, TypeExpression)
           [Restriction] Relation
        -- ^ A relation corresponding to a type abstraction.

  | FunAbs RelationInfo (Either TermVariable TermVariable)
           (TypeExpression, TypeExpression) [Restriction] Relation
        -- ^ A quantified function.

  deriving (Typeable, Data, Eq)



-- | Extracts the relation information from a relation.

relationInfo :: Relation -> RelationInfo
relationInfo rel = case rel of
  RelVar ri _       -> ri
  FunVar ri _       -> ri
  RelBasic ri       -> ri
  RelLift ri _ _    -> ri
  RelFun ri _ _     -> ri
  RelFunLab ri _ _  -> ri
  RelAbs ri _ _ _ _ -> ri
  FunAbs ri _ _ _ _ -> ri



-- | The relation information stored with every relation.

data RelationInfo = RelationInfo
  { relationLanguageSubset :: LanguageSubset
        -- ^ The language subset in which a relation was generated.
  
  , relationLeftType       :: TypeExpression
        -- ^ The type of the first components of pairs contained in a relation.
  
  , relationRightType      :: TypeExpression
        -- ^ The type of the second components of pairs contained in a 
        --   relation.
  
  }
  deriving (Typeable, Data, Eq)



-- | A relation variable.

newtype RelationVariable = RVar String
  deriving (Typeable, Data, Eq)



-- | Describes unfolded lift relations.

data UnfoldedLift = UnfoldedLift Relation [UnfoldedDataCon]
  deriving (Typeable, Data)



-- | A relational descriptions of a data constructor.

data UnfoldedDataCon
  = BotPair
  | ConPair DataConstructor
  | ConMore DataConstructor [TermVariable] [TermVariable] Formula
  deriving (Typeable, Data)



-- | Data constructors.

data DataConstructor
  = DConEmptyList   -- ^ The nullary data constructor @[]@.
  | DConConsList    -- ^ The binary data constructor @:@.
  | DConTuple Int   -- ^ The n-ary tuple data constructor.
  | DCon String     -- ^ Any other data constructor.
  deriving (Typeable, Data)



-- | A relational description of a class declaration.

data UnfoldedClass 
  = UnfoldedClass [TypeClass] TypeClass (Either RelationVariable TermVariable)
                  [Formula]
  deriving (Typeable, Data)



