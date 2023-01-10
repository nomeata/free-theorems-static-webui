{-# LANGUAGE ExistentialQuantification, Rank2Types #-}


-- | Defines standard functions for modifying type expressions or retrieving
--   information from type expressions.

module Language.Haskell.FreeTheorems.Frontend.TypeExpressions (
    freeTypeVariables
  , allTypeVariables
  , createNewTypeVariableNotIn
  , alphaConversion
  , substituteTypeVariables
  , replaceAllTypeSynonyms
  , closeTypeExpressions
  , closureFor
) where



import Data.Generics
    ( Typeable, Data, synthesize, mkQ, everywhere, mkT, gmapT, GenericQ
    , GenericT )
import Data.List (find)
import Data.Set as Set
    ( Set, empty, union, insert, delete, fold, unions, difference, singleton
    , member )
import Data.Map as Map (Map, empty, lookup, delete, insert)
import Data.Maybe (maybe, fromJust)

import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.NameStores (typeNameStore)





------- Functions for type variables ------------------------------------------


-- | Returns all type variables occurring in a type expression.

allTypeVariables :: TypeExpression -> Set.Set TypeVariable
allTypeVariables = synthesize Set.empty Set.union (id `mkQ` update)
  where
    update t s = case t of
      TypeVar v        -> Set.insert v s
      TypeAbs v _ _    -> Set.insert v s
      TypeAbsLab v _ _ -> Set.insert v s
      otherwise        -> s



-- | Returns the free type variables of a type expression.

freeTypeVariables :: TypeExpression -> Set.Set TypeVariable
freeTypeVariables = synthesize Set.empty Set.union (id `mkQ` update)
  where
    update t s = case t of
      TypeVar v        -> Set.insert v s
      TypeAbs v _ _    -> Set.delete v s
      TypeAbsLab v _ _ -> Set.delete v s
      otherwise        -> s



-- | Substitutes every free occurrence of all type variables given in the map
--   with the type expressions they are mapped to.

substituteTypeVariables ::
    Map.Map TypeVariable TypeExpression 
    -> TypeExpression 
    -> TypeExpression

substituteTypeVariables env t = 
  everywhereWith (id `mkQ` update) (mkTw substitute) env t
  where
    -- Updates the environment used in the top-down traversal.
    -- Removes bound type variables from the mapping. Thus, these variables
    -- won't be replaced in the second stage.
    update t env = case t of
      TypeAbs v _ _    -> Map.delete v env
      TypeAbsLab v _ _ -> Map.delete v env
      otherwise        -> env
    
    -- Replaces a type variable by a type expression, if the type variable is
    -- contained in the environment.
    substitute env t = case t of
      TypeVar v -> maybe t id (Map.lookup v env)
      otherwise -> t



-- | Creates a new type variable not occurring in the given set of type
--   variables.
--
--   A type variable can either be named by the letters \'a\' to \'e\' or, if
--   that causes conflicts, by the letter \'a\' concatenated with a number
--   starting from 1.

createNewTypeVariableNotIn :: Set.Set TypeVariable -> TypeVariable
createNewTypeVariableNotIn forbiddenVars =
  let vars = map (TV . Ident) typeNameStore
   in fromJust $ find (\v -> not (v `Set.member` forbiddenVars)) vars



-- | Replaces every bound occurrence of the given type variable in the given
--   type expression with a new type variable which is created by
--   'createNewTypeVariableNotIn'.
--
--   Several bound occurrences of the given type variable are replaced with the
--   same new type variable. Only one new type variable is created altogether.

alphaConversion :: TypeVariable -> TypeExpression -> TypeExpression
alphaConversion old t =
  everywhereWith (id `mkQ` change) (mkTw replace) id t
  where
    -- The new type variable which will replace 'old' everywhere in the given
    -- type expression.
    new = createNewTypeVariableNotIn (allTypeVariables t)
    
    -- This function replaces any type variable equal to 'old' with 'new' and
    -- keeps all other type variables unchanged.
    rep v = if (v == old) then new else v

    -- Modifies the function which replaces type variables.
    -- If we are at the type abstraction where 'old' is bound, then 'old' has
    -- to be replaced in every subexpression by the new type variable.
    change t f = case t of
      TypeAbs    v _ _ -> if (v == old) then rep else f
      TypeAbsLab v _ _ -> if (v == old) then rep else f
      otherwise         -> f

    -- Applies the current replacement function to type variables.
    -- In type abstractions, the static function 'rep' is used to replace
    -- 'old' with 'new' or otherwise keep the type variable.
    -- Note that - independent of the usage of 'rep' - the replacement function
    -- 'r' will be modified by 'change' when advancing to subexpressions.
    replace r t = case t of
      TypeVar    v       -> TypeVar    (r v)
      TypeAbs    v cs t' -> TypeAbs    (rep v) cs t'
      TypeAbsLab v cs t' -> TypeAbsLab (rep v) cs t'
      otherwise       -> t





------- Generic helper definitions --------------------------------------------


-- | Generic transformations using a value of fixed type.

type GenericTw u = forall a . Data a => u -> a -> a



-- | Make a generic transformation which uses a value of fixed type.
--   This function takes a specific case into a general case, such that no
--   transformation is applied for types not covered by the specific case.

mkTw :: (Typeable a, Typeable b) => (u -> a -> a) -> u -> b -> b
mkTw f u = mkT $ f u



-- | Pushes a value in a top-down fashion trough a tree and applies that value
--   from bottom to top to every node.
--
--   More detailed, the expression
--
-- >   everywhereWith update apply v
--
--   is evaluated as follows:
--   The value @v@ is transfered through the tree from top to bottom while,
--   at every node, the function @update@ is applied to it. This allows the
--   initial value to be changed like, for example, an environment gathering
--   information from the root to the leaf while moving through the tree.
--   Thereafter, the transformation function @apply@ is applied to every node
--   from bottom to top. It might use the value distributed to that node.

everywhereWith :: GenericQ (u -> u) -> GenericTw u -> u -> GenericT
everywhereWith k f u x = (f u) $ gmapT (everywhereWith k f (k x u)) x





------- Replacing type synonyms -----------------------------------------------


-- | Replaces all type synonyms in an arbitrary tree.
--   The first argument gives the list of known type synonyms and their 
--   declarations. Every occurrence of one of those type synonyms in the second
--   argument is replaced by the according right-hand side of the declaration.
--   
--   Note that the type synonym declarations given in the first argument may
--   themselves contain type synonyms. However, type synonym declarations must
--   not be recursive nor mutually recursive.

replaceAllTypeSynonyms :: (Typeable a, Data a) => [TypeDeclaration] -> a -> a
replaceAllTypeSynonyms knownTypes = everywhere (mkT replace)
    -- This functions replaces all type synonyms in a bottom-up manner.
    -- Thus, when applying 'replace', all type synonyms are already removed
    -- from all children of the node.

  where
    -- Replacing type synonyms only affects type constructors.
    -- Check if there is a type synonym declaration for the given type 
    -- constructor. If not, just return the unchanged type expression.
    -- Otherwise replace the type synonym by its definition.
    replace t = case t of
      TypeCon c ts -> maybe t (applyTypeSynonym ts) (findTypeDecl knownTypes c)
      otherwise    -> t

    -- Applies the declaration of a type synonym to a list of type expressions.
    -- The type expression composed in this way is returned.
    -- Note that the structure of 'replaceTypeSynonyms' guarantees that there is
    -- no type synonym in any of the type expressions of 'ts'.
    applyTypeSynonym ts (Type _ vs t) =
      let 
          -- First, remove all type synonyms from the declaration's right-hand
          -- side. Note that this terminates because type expressions cannot be
          -- declared recursively nor mutually recursively.
          t1 = replaceAllTypeSynonyms knownTypes t

          -- Construct an environment to be used to substitute every free
          -- variable in 't' by the appropiate type expression of 'ts'.
          env = foldr (uncurry Map.insert) Map.empty (zip vs ts)

          -- Rename all bound variables in 't' such that no free variables of
          -- any type expression in 'ts' will get bound.
          allFreeVariables = Set.unions $ map freeTypeVariables ts
          t2 = Set.fold alphaConversion t1 allFreeVariables

          -- Finally, apply the declaration's right-hand side to 'ts' and return
          -- the constructed type expression.
       in substituteTypeVariables env t2
  


-- | Looks up the declaration for a type synonym constructor.
--   If the given type constructor is not a type synonym or there is no
--   declaration for this type constructor in the declarations list, then
--   @Nothing@ is returned.

findTypeDecl :: [TypeDeclaration] -> TypeConstructor -> Maybe TypeDeclaration
findTypeDecl decls con = case con of
  Con name  -> find (\d -> typeName d == name) decls 
  otherwise -> Nothing





------- Closing type expressions ----------------------------------------------


-- | Closes all type expressions in type signature declarations.
--   Class methods are also modified, in that every free variable expect the
--   class variable is explicitly bound.

closeTypeExpressions :: [Declaration] -> [Declaration]
closeTypeExpressions = map closeDecl
  where
    closeDecl d = case d of
      ClassDecl d -> ClassDecl (closeClassDecl d)
      TypeSig sig -> TypeSig (closeSignature sig)
      otherwise   -> d



-- | Closes type signatures of class methods. Afterwards, the class variable is
--   still free in all class methods.

closeClassDecl :: ClassDeclaration -> ClassDeclaration
closeClassDecl d =
  d { classFuns = map (closureWithout (classVar d)) (classFuns d) }
  where
    -- Close the class method signature while keeping the class variable free.
    closureWithout v s = 
      let t = signatureType s
          freeVars = freeTypeVariables t `Set.difference` Set.singleton v
       in s { signatureType = closureFor freeVars t }



-- | Close a type signature declaration.

closeSignature :: Signature -> Signature
closeSignature s =
  let t = signatureType s
   in s { signatureType = closureFor (freeTypeVariables t) t }



-- | Explicitly binds all type variables of the first argument by a type 
--   abstraction in the given type expression.

closureFor :: Set.Set TypeVariable -> TypeExpression -> TypeExpression
closureFor vs t = Set.fold (\v -> TypeAbs v []) t vs






