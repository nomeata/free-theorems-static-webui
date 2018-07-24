{-# LANGUAGE FlexibleContexts #-}

-- | Declares an intermediate data structure along with a function to transform
--   type signatures into the intermediate structure. There are also other
--   functions working on intermediate structures, namely to retrieve relation
--   variables and to instantiate them to functions.

module Language.Haskell.FreeTheorems.Intermediate (
    Intermediate (..)
  , interpret
  , interpretM
  , relationVariables
  , specialise
  , specialiseInverse
) where



import Control.Monad (liftM, liftM2, mapM)
import Control.Monad.Reader (ReaderT, ask, runReaderT, local)
import Control.Monad.State (State, get, put, runState)
import Control.Monad.Trans (lift)
import Data.Generics ( Typeable, Data, everywhere, everything, listify, mkT
                     , mkQ, extQ)
import qualified Data.Map as Map (Map, empty, lookup, insert, map)

import Language.Haskell.FreeTheorems.LanguageSubsets
import Language.Haskell.FreeTheorems.Syntax 
import Language.Haskell.FreeTheorems.ValidSyntax
import Language.Haskell.FreeTheorems.Theorems
import Language.Haskell.FreeTheorems.Frontend.TypeExpressions
    ( substituteTypeVariables )
import Language.Haskell.FreeTheorems.NameStores 
    ( relationNameStore, typeExpressionNameStore, functionNameStore1, functionNameStore2 )


-- helper to stay compatible with new Map.lookup for base >= 4.0.0.0
maybeToMonad :: Monad m => Maybe a -> m a
maybeToMonad mb = 
    case mb of
    Just x  -> return x
    Nothing -> fail "Data.Map.lookup: Key not found"

------- Intermediate data structure -------------------------------------------


-- | A structure describing the intermediate result of interpreting a type
--   expression as a relation.

data Intermediate = Intermediate 
  { intermediateName      :: String 
        -- ^ The name of the symbol for which the theorem is to be generated.
  
  , intermediateSubset    :: LanguageSubset
        -- ^ The language subset in which the theorem is to be generated.
  
  , intermediateRelation :: Relation
        -- ^ The relation obtained from the type.
  
  , functionVariableNames1 :: [String]
        -- ^ A name store for new, fresh function names.
        --   This is needed because functions can be specialised step-by-step
        --   after having generated the first relation from a type.

  , functionVariableNames2 :: [String]
        -- ^ Another name store for new, fresh function names, disjoint from
        --   the one above.

  , signatureNames :: [String]
        -- ^ The names of all known signatures. These names must not be used to
        --   generate names of functions and variables.
  
  , interpretNameStore :: NameStore 
        -- ^ A name store to generate new relation variables and type
        --   expressions.
  
  }





------- Interpret types as relations ------------------------------------------



-- | Interprets a valid signature as a relation. This is the key point for
--   generating free theorems.

interpret :: 
    [ValidDeclaration] -> LanguageSubset -> ValidSignature -> Maybe Intermediate
interpret vds l s =
  let n  = unpackIdent . signatureName . rawSignature $ s
      ss = getSignatureNames (map rawDeclaration vds)
      fs = n : ss
      t  = signatureType . rawSignature $ s
      (i, rs) = runState (runReaderT (interpretM l t) Map.empty) (initialState fs)
      r = Intermediate n l i (filter (`notElem` fs) functionNameStore1) (filter (`notElem` fs) functionNameStore2) ss rs
   in case l of
        SubsetWithSeq _ -> Just r
        otherwise       -> if containsStrictTypes vds s 
                             then Nothing
                             else Just r
  where
    getSignatureNames = everything (++) ([] `mkQ` getSigName)
    getSigName (Signature i _) = [unpackIdent i]

    containsStrictTypes vds s = 
      let rs = rawSignature s
          ns = everything (++) ([] `mkQ` getCons `extQ` getClasses) rs
          ds = map (getDeclarationName . rawDeclaration) 
                   (filter isStrictDeclaration vds)
          isStrict n = n `elem` ds
       in any isStrict ns

    getCons c = case c of { Con n -> [n] ; otherwise -> [] }
    getClasses (TC n) = [n]



-- | Transforms a type expression into a relation. The environment is used to
--   map seen type variables to newly created relation variables. The state
--   serves for creating relation variables.

interpretM :: 
    LanguageSubset 
    -> TypeExpression 
    -> ReaderT Environment (State NameStore) Relation

interpretM l t = case t of

    -- get the environment from the reader, lookup the relation variable for
    -- the given type variable (this operation will never fail because
    -- in the initial type expression, all occurring type variables are bound
    -- by type abstraction which are resolved by updating the environment, see
    -- below) and create a relation consisting solely of the relation variable
  TypeVar v -> maybeToMonad.Map.lookup v =<< ask
  
    -- either create a basic relation or a lift relation, depending on the 
    -- subtypes
  TypeCon c ts -> do
    rs <- mapM (interpretM l) ts   -- interpret the subtypes
    ri <- mkRelationInfo l t       -- create the relation info
        
        -- checks if an intermediate relation is a basic case
    let basic rel = case rel of { RelBasic _ -> True ; otherwise -> False }

        -- create a basic intermediate relation if all subrelations are basic
        -- (or if there is no subrelation), otherwise create a lifted relation
    if all basic rs
      then return (RelBasic (RelationInfo l t t))
      else return (RelLift ri c rs)

    -- create a relation for function types
  TypeFun t1 t2 -> do
    ri <- mkRelationInfo l t       -- create the relation info
    liftM2 (RelFun ri) (interpretM l t1) (interpretM l t2)

    -- create a second relation for function types (used only for language
    -- subset with seq and the equational setting
  TypeFunLab t1 t2 -> do
    ri <- mkRelationInfo l t       -- create the relation info
    liftM2 (RelFunLab ri) (interpretM l t1) (interpretM l t2)

    -- create a relation for type abstractions
  TypeAbs v cs t' -> do
    ri <- mkRelationInfo l t                    -- create the relation info
    (rv, t1, t2) <- lift newRelationVariable    -- create a new variable
    let rvar = RelVar (RelationInfo l t1 t2) rv
    r  <- local (Map.insert v rvar) $ interpretM l t'  -- subrelations
    let res = relRes l ++ (if null cs then [] else [RespectsClasses cs])
    return (RelAbs ri rv (t1,t2) res r)

    -- create a second relation for type abstractions (used only for language
    -- subset with seq and the equational setting
  TypeAbsLab v cs t' -> do
    ri <- mkRelationInfo l t                    -- create the relation info
    (rv, t1, t2) <- lift newRelationVariable    -- create a new variable
    let rvar = RelVar (RelationInfo l t1 t2) rv
    r  <- local (Map.insert v rvar) $ interpretM l t'  -- subrelations
    let res = (filter (/= BottomReflecting) (relRes l)) ++ (if null cs then [] else [RespectsClasses cs])
    return (RelAbs ri rv (t1,t2) res r)

  where
    mkRelationInfo l t = do
      env <- ask
        -- create the 'left' and 'right' type expression of 't',
        -- i.e. replace all free variables by the left or right type
        -- expressions of the corresponding relation variable
      let getLt = relationLeftType . relationInfo
      let getRt = relationRightType . relationInfo
      let lt = substituteTypeVariables (Map.map getLt env) t
      let rt = substituteTypeVariables (Map.map getRt env) t
      return (RelationInfo l lt rt)


    -- Returns the restrictions for relations, depending on the current
    -- language subset and theorem type.
    relRes l = case l of
      BasicSubset                       -> [ ]
      SubsetWithFix EquationalTheorem   -> [ Strict, Continuous ]
      SubsetWithFix InequationalTheorem -> [ Strict, Continuous
                                           , LeftClosed ]
      SubsetWithSeq EquationalTheorem   -> [ Strict, Continuous
                                           , BottomReflecting ]
      SubsetWithSeq InequationalTheorem -> [ Strict, Continuous, Total
                                           , LeftClosed ]
   




------- Helper definitions for the interpretation -----------------------------


-- | An environment mapping type variables to intermediate relation variables
--   (stored as relations).

type Environment = Map.Map TypeVariable Relation 



-- | Represents the names of future variable names. The first component provides
--   names for relations, while the second component provides names for type
--   expressions.

type NameStore = ([String], [TypeExpression])



-- | Initialises the name store. Both components of the name store are infinite
--   list.
--   For more information, see 'Language.Haskell.FreeTheorems.NameStore'.

initialState :: [String] -> NameStore
initialState ns = 
   ( relationNameStore
   , map (TypeExp . TF . Ident) . filter (`notElem` ns)
         $ typeExpressionNameStore )



-- | Creates a new relation variable using the name store.

newRelationVariable :: 
    State NameStore (RelationVariable, TypeExpression, TypeExpression)
newRelationVariable = do
  (rvs, ts) <- get
  let ([rv], rvs') = splitAt 1 rvs
  let ([t1, t2], ts') = splitAt 2 ts
  put (rvs', ts') 
  return (RVar rv, t1, t2)





------- Instantiation of relation variables -----------------------------------


-- | Creates a list of all bound relation variables in an intermediate
--   structure, which can be specialised to a function. 

relationVariables :: Intermediate -> [RelationVariable]
relationVariables (Intermediate _ _ rel _ _ _ _) = getRVar True rel
  where
    getRVar ok rel = case rel of
      RelLift _ _ rs    -> concatMap (getRVar ok) rs
      RelFun _ r1 r2    -> getRVar (not ok) r1 ++ getRVar ok r2
      RelFunLab _ r1 r2 -> getRVar (not ok) r1 ++ getRVar ok r2
      RelAbs _ rv _ _ r -> (if ok then [rv] else []) ++ getRVar ok r
      FunAbs _ _ _ _ r  -> getRVar ok r 
      otherwise         -> []



-- | Specialises a relation variable to a function variable in an intermediate
--   structure.

specialise :: Intermediate -> RelationVariable -> Intermediate
specialise ir rv = reduceLifts (replaceRelVar ir rv Left)



-- | Specialises a relation variable to an inverse function variable.
--   This function does not modify intermediate structures in subsets with
--   equational theorems.

specialiseInverse :: Intermediate -> RelationVariable -> Intermediate
specialiseInverse ir rv = 
  case theoremType (intermediateSubset ir) of
    EquationalTheorem   -> ir
    InequationalTheorem -> reduceLifts  (replaceRelVar ir rv Right)



-- | Replaces a relation variable with a function variable.

replaceRelVar :: 
    Intermediate -> RelationVariable 
    -> (TermVariable -> Either TermVariable TermVariable) -> Intermediate
replaceRelVar ir (RVar rv) leftOrRight =
  let ([funName], fns) = splitAt 1 (functionVariableNames1 ir)
      fv = leftOrRight . TVar $ funName
      relation = intermediateRelation ir
   in ir { intermediateRelation  = everywhere (mkT $ replace rv fv) relation
         , functionVariableNames1 = drop 1 (functionVariableNames1 ir)
         }
  where
    -- perform the actual replacement
    -- when replacing a relation by a 'right' function in a relation
    -- abstraction, the types have to be flipped
    replace rv fv rel = case rel of
      RelVar ri (RVar r) -> 
        let tv = either (Left . TermVar) (Right . TermVar) fv
         in if rv == r then FunVar ri tv else rel
      RelAbs ri (RVar r) ts res rel' ->
        let res'' = either (const funResL) (const funResR) fv
            -- hack! should be somehow better implemented
	    -- if BottomReflecting is not present, we had
            -- TypeAbsLab quantification in (SubsetWithSeq Equational)
            res'  = if elem BottomReflecting res || elem Total res then res'' else filter (/= Total) res''
         in if rv == r
              then FunAbs ri fv ts (res' ++ (classConstraints res)) rel'
              else rel
      otherwise -> rel

    -- the restrictions for functions in the equational setting and for
    -- 'left' functions in inequational settings
    funResL = case intermediateSubset ir of
      BasicSubset     -> [ ]
      SubsetWithFix _ -> [ Strict ]
      SubsetWithSeq _ -> [ Strict, Total ]
    
    -- the restrictions for 'right' functions in the inequational settings
    funResR = case intermediateSubset ir of
      BasicSubset     -> [ ]
      SubsetWithFix _ -> [ ]
      SubsetWithSeq _ -> [ Strict ]

    -- returns the class constraints
    classConstraints res = filter isCC res
      where 
        isCC r = case r of { RespectsClasses _ -> True ; otherwise -> False }



-- | Applies simplifications on lifted constructors. 
--   If the argument is a function then lifted lists are replaced by map and
--   lifted Maybes are replaced by fmap.

reduceLifts :: Intermediate -> Intermediate
reduceLifts ir = 
--  ir { intermediateRelation = reduceEverywhere (intermediateRelation ir) }
  ir { intermediateRelation = re True (intermediateRelation ir) }
  where
--    reduceEverywhere = everywhere (mkT reduce)

    re ok rel = case rel of
      RelLift ri con rs     -> if ok 
                                 then reduce (RelLift ri con (map (re ok) rs))
                                 else rel
      RelFun ri r1 r2       -> RelFun ri (re (mk' (not ok) ri r1) r1) 
                                         (re (mk ok ri r2) r2)
      -- second logical relation for functions. Only used for the language
      -- subset with Seq in the equational setting
      RelFunLab ri r1 r2    -> RelFunLab ri (re (mk' (not ok) ri r1) r1) 
                                            (re (mk ok ri r2) r2)
      RelAbs ri rv ts res r -> RelAbs ri rv ts res (re ok r)
      FunAbs ri fv ts res r -> FunAbs ri fv ts res (re ok r)
      otherwise             -> rel

    mk' ok ri r = case theoremType (relationLanguageSubset ri) of
                    EquationalTheorem   -> True
                    InequationalTheorem -> 
                      case r of
                        RelLift _ ConList _ -> True
                        otherwise           -> ok


    mk ok ri r = case theoremType (relationLanguageSubset ri) of
                   EquationalTheorem   -> True
                   InequationalTheorem -> ok


    -- Transforms a lifted constructor to a function, if possible.
    -- This function is applied in a bottom-up manner, therefore the
    -- arguments of the lifted constructor are already reduced.
    reduce rel = case rel of
      RelLift ri con rs -> maybe rel id (toTerm ri con rs)
      otherwise         -> rel

    -- Tries to transform a lifted relation. If not succesful, Nothing is
    -- returned.
    toTerm ri con rs = do
      f <- funSymbol con
      -- first check if all arguments are 'left' functions
      case mapM leftFun rs of
        Just fts -> Just . FunVar ri . Left $ term f fts
        Nothing  -> -- then check if all arguments are 'right' functions
                    case mapM rightFun rs of
                      Just fts -> Just . FunVar ri . Right $ term f fts
                      Nothing  -> Nothing

    -- Returns the function symbol associated with a lifted constructor.
    funSymbol con = case con of
      ConList             -> Just . TVar $ "map"
      Con (Ident "Maybe") -> Just . TVar $ "fmap"
      otherwise           -> Nothing

    -- Checks if 'rel' is a 'left' function. If so, its term and type is
    -- returned, otherwise Nothing.
    leftFun rel = case rel of
      FunVar ri (Left f) -> Just (f, ( relationLeftType ri
                                     , relationRightType ri))
      otherwise          -> Nothing

    -- Checks if 'rel' is a 'right' function. If so, its term and type is
    -- returned, otherwise Nothing.
    -- The returned type is flipped mirroring the fact that right functions are
    -- actually inverse functions.
    rightFun rel = case rel of
      FunVar ri (Right f) -> Just (f, ( relationRightType ri
                                      , relationLeftType ri))
      otherwise           -> Nothing

    -- Creates a term by instantiating 'f' and applying the arguments of 'fts'.
    term f fts = 
        let (fs, ts) = unzip fts
            termins t (t1, t2) = TermIns (TermIns t t1) t2
         in foldl TermApp (foldl termins (TermVar f) ts) fs
      





