{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 610
{-# LANGUAGE ScopedTypeVariables #-}
#else
{-# LANGUAGE PatternSignatures #-}
#endif

module Language.Haskell.FreeTheorems.Unfold (
    asTheorem
  , asCompleteTheorem
  , unfoldFormula
  , unfoldLifts
  , unfoldClasses
) where



import Control.Monad (liftM)
import Control.Monad.State (StateT, get, put, evalStateT, evalState)
import Control.Monad.Reader (Reader, ask, local, runReader, runReaderT)
import Data.Generics (everything, extQ, listify, Data, mkQ)
import Data.List (unfoldr, nub, find, (\\), nubBy)
import Data.Map as Map (fromList)
import Data.Maybe (fromJust)

import Language.Haskell.FreeTheorems.BasicSyntax
import Language.Haskell.FreeTheorems.ValidSyntax
import Language.Haskell.FreeTheorems.LanguageSubsets
import Language.Haskell.FreeTheorems.Intermediate
import Language.Haskell.FreeTheorems.Theorems
import Language.Haskell.FreeTheorems.NameStores




------- Basic structures and functions ----------------------------------------


-- | Abbreviation for the state used to unfold relations to theorems.

type Unfolded a = StateT UnfoldedState (Reader (Bool,Bool)) a



-- | The state used to unfold relations to theorems.

data UnfoldedState = UnfoldedState 
  { newVariableNames :: [String]
        -- ^ An infinite list storing names for variables.
        --   Every element of this list is distinct to the elements of
        --   'newFunctionNames1' and 'newFunctionNames2'.
  
  , newFunctionNames1 :: [String]
        -- ^ An infinite list storing names for functions.
        --   Every element of this list is distinct to the elements of
        --   'newVariableNames' and 'newFunctionNames2'.

  , newFunctionNames2 :: [String]
        -- ^ Another infinite list storing names for functions.
        --   Every element of this list is distinct to the elements of
        --   'newVariableNames' and 'newFunctionNames1'.
  }
  


-- | Create the initial name store which serves for creating new variable names.

initialState :: Intermediate -> UnfoldedState
initialState ir = 
  let fs = intermediateName ir : signatureNames ir
   in UnfoldedState
        { newVariableNames = filter (`notElem` fs) variableNameStore
          -- variable names must not equal the name of the intermediate
          -- variable names don't ever collide with function names or names of
          -- fixed type expressions (see 'NameStores' module)
  
        , newFunctionNames1 = functionVariableNames1 ir
          -- take the name store of functions which was already used during
          -- generation and modification of the intermediate relations

        , newFunctionNames2 = functionVariableNames2 ir
          -- take the name store of functions which was already used during
          -- generation and modification of the intermediate relations
        }
        


-- | Creates a new term variable. The name is chosen depending on the given
--   type expression, i.e. either a function variable name or a variable name
--   is returned.

newVariableFor :: TypeExpression -> Unfolded TermVariable
newVariableFor t = do
  case t of
    TypeFun _ _    -> do state <- get
                         let ([f], fs) = splitAt 1 (newFunctionNames2 state)
                         put (state { newFunctionNames2 = fs })
                         return (TVar f)

    TypeFunLab _ _ -> do state <- get
                         let ([f], fs) = splitAt 1 (newFunctionNames2 state)
                         put (state { newFunctionNames2 = fs })
                         return (TVar f)
    
    TypeAbs _ _ t' -> newVariableFor t'
    
    otherwise      -> do state <- get
                         let ([x], xs) = splitAt 1 (newVariableNames state)
                         put (state { newVariableNames = xs })
                         return (TVar x)



-- | Checks if simplifications are possible.

simplificationsAllowed :: Unfolded Bool
simplificationsAllowed = do
  (simplificationPossible, allowAnySimplification) <- ask
  if allowAnySimplification
    then return simplificationPossible
    else return False




-- | Toggles the simplification state in the unfolding of the argument.

toggleSimplifications :: Unfolded a -> Unfolded a
toggleSimplifications = local (\(p,a) -> (not p, a))





------- Unfolding formulas ----------------------------------------------------


-- | Unfolds an intermediate structure to a theorem.

asTheorem :: Intermediate -> Theorem
asTheorem i = 
  let v = TermVar . TVar . intermediateName $ i
      r = intermediateRelation i
      s = initialState i
   in runReader (evalStateT (unfoldFormula v v r) s) (True, True)


-- | Unfolds an intermediate structure to a theorem with _all_ restrictions.

asCompleteTheorem :: Intermediate -> Theorem
asCompleteTheorem i = 
  let v = TermVar . TVar . intermediateName $ i
      r = intermediateRelation i
      s = initialState i
   in runReader (evalStateT (unfoldFormula v v r) s) (True, False)


-- | Unfolds the logical relation "R" in the expression "(x,y) in R" to a
--   theorem. It works by recursively applying unfolding operations of
--   relational actions.

unfoldFormula :: Term -> Term -> Relation -> Unfolded Formula
unfoldFormula x y rel = case rel of
  RelVar _ _           -> return . Predicate . IsMember x y $ rel
  FunVar ri term       -> unfoldTerm x y ri term
  RelBasic ri          -> unfoldBasic x y ri
  RelLift _ _ _        -> return . Predicate . IsMember x y $ rel
  RelFun ri r1 r2      -> unfoldFun x y ri r1 r2
  RelFunLab ri r1 r2   -> unfoldFunLab x y ri r1 r2
  RelAbs ri v ts res r -> unfoldAbsRel x y ri v ts res r
  FunAbs ri v ts res r -> unfoldAbsFun x y ri v ts res r



-- | Unfolding operation for terms, i.e. relations specialised to functions.

unfoldTerm :: 
    Term -> Term -> RelationInfo -> Either Term Term -> Unfolded Formula
unfoldTerm x y ri term = return . Predicate $
  case term of
    Left t  -> case theoremType (relationLanguageSubset ri) of
                 EquationalTheorem   -> IsEqual (TermApp t x) y
                 InequationalTheorem -> IsLessEq (TermApp t x) y
    Right t -> IsLessEq x (TermApp t y)



-- | Unfolding operation for nullary relational actions.

unfoldBasic :: Term -> Term -> RelationInfo -> Unfolded Formula
unfoldBasic x y ri = return . Predicate $
  case theoremType (relationLanguageSubset ri) of
    EquationalTheorem   -> IsEqual  x y
    InequationalTheorem -> IsLessEq x y
  


-- | Unfolding operation for relational actions of type abstractions.

unfoldAbsRel :: 
    Term -> Term -> RelationInfo 
    -> RelationVariable -> (TypeExpression, TypeExpression)
    -> [Restriction] -> Relation -> Unfolded Formula

unfoldAbsRel x y ri v (t1,t2) res rel = do
  rightSide <- unfoldFormula (TermIns x t1) (TermIns y t2) rel
  return (ForallRelations v (t1, t2) res rightSide)



-- | Unfolding operation for relational actions of type abstractions
--   (for an abstraction of a function).

unfoldAbsFun :: 
    Term -> Term -> RelationInfo 
    -> Either TermVariable TermVariable -> (TypeExpression, TypeExpression)
    -> [Restriction] -> Relation -> Unfolded Formula

unfoldAbsFun x y ri v (t1,t2) res rel = do
  rightSide <- unfoldFormula (TermIns x t1) (TermIns y t2) rel
  return (ForallFunctions v (t1, t2) res rightSide)



-- | Unfolding operation for relational actions of function type constructors.

unfoldFun :: 
    Term -> Term -> RelationInfo -> Relation -> Relation -> Unfolded Formula
unfoldFun x y ri rel1 rel2 =
  case rel1 of
    RelVar _ _          -> unfoldFunPairs x y ri rel1 rel2
    FunVar _ t          -> 
      let ta = either (\t -> Left (TermApp t)) (\t -> Right (TermApp t)) t
          one = unfoldFunOneVar x y ri ta rel1 rel2
          two = unfoldFunVars x y ri rel1 rel2
       in case theoremType (relationLanguageSubset ri) of
            EquationalTheorem   -> one
            InequationalTheorem -> do
              simple <- simplificationsAllowed
              if simple then one else two
    RelBasic _          -> 
      case theoremType (relationLanguageSubset ri) of
        EquationalTheorem   -> unfoldFunOneVar x y ri (Left id) rel1 rel2
        InequationalTheorem -> unfoldFunVars x y ri rel1 rel2
    RelLift _ _ _       -> unfoldFunPairs x y ri rel1 rel2
    RelFun _ _ _        -> unfoldFunVars x y ri rel1 rel2
    RelFunLab _ _ _     -> unfoldFunVars x y ri rel1 rel2
    RelAbs _ _ _ r _    -> unfoldFunVars x y ri rel1 rel2
    FunAbs _ _ _ _ _    -> unfoldFunVars x y ri rel1 rel2

-- | Unfolding operation for relational actions of function type constructors.

unfoldFunLab :: 
    Term -> Term -> RelationInfo -> Relation -> Relation -> Unfolded Formula
unfoldFunLab x y ri rel1 rel2 =
  case rel1 of
    RelVar _ _          -> unfoldFunLabPairs x y ri rel1 rel2
    FunVar _ t          -> 
      let ta = either (\t -> Left (TermApp t)) (\t -> Right (TermApp t)) t
          one = unfoldFunLabOneVar x y ri ta rel1 rel2
          two = unfoldFunLabVars x y ri rel1 rel2
       in case theoremType (relationLanguageSubset ri) of
            EquationalTheorem   -> one
            InequationalTheorem -> do
              simple <- simplificationsAllowed
              if simple then one else two
    RelBasic _          -> 
      case theoremType (relationLanguageSubset ri) of
        EquationalTheorem   -> unfoldFunLabOneVar x y ri (Left id) rel1 rel2
        InequationalTheorem -> unfoldFunLabVars x y ri rel1 rel2
    RelLift _ _ _       -> unfoldFunLabPairs x y ri rel1 rel2
    RelFun _ _ _        -> unfoldFunLabVars x y ri rel1 rel2
    RelFunLab _ _ _     -> unfoldFunLabVars x y ri rel1 rel2
    RelAbs _ _ _ r _    -> unfoldFunLabVars x y ri rel1 rel2
    FunAbs _ _ _ _ _    -> unfoldFunLabVars x y ri rel1 rel2



unfoldFunOneVar :: 
    Term -> Term -> RelationInfo -> Either (Term -> Term) (Term -> Term) 
    -> Relation -> Relation -> Unfolded Formula
unfoldFunOneVar x y ri termapp rel1 rel2 = do
  let t = either (const (relationLeftType (relationInfo rel1))) 
                 (const (relationRightType (relationInfo rel1)))
                 termapp
  
  x' <- newVariableFor t
  let tx' = TermVar x'

  f <- case termapp of
         Left t  -> unfoldFormula (TermApp x tx') (TermApp y (t tx')) rel2
         Right t -> unfoldFormula (TermApp x (t tx')) (TermApp y tx') rel2

  addRestriction x y (relationLanguageSubset ri) (ForallVariables x' t f)
--  return (ForallVariables x' t f)

unfoldFunLabOneVar :: 
    Term -> Term -> RelationInfo -> Either (Term -> Term) (Term -> Term) 
    -> Relation -> Relation -> Unfolded Formula
unfoldFunLabOneVar x y ri termapp rel1 rel2 = do
  let t = either (const (relationLeftType (relationInfo rel1))) 
                 (const (relationRightType (relationInfo rel1)))
                 termapp
  
  x' <- newVariableFor t
  let tx' = TermVar x'

  f <- case termapp of
         Left t  -> unfoldFormula (TermApp x tx') (TermApp y (t tx')) rel2
         Right t -> unfoldFormula (TermApp x (t tx')) (TermApp y tx') rel2

-- addRestriction x y (relationLanguageSubset ri) (ForallVariables x' t f)
  return (ForallVariables x' t f)


unfoldFunPairs :: 
    Term -> Term -> RelationInfo -> Relation -> Relation -> Unfolded Formula
unfoldFunPairs x y ri rel1 rel2 = do
  x' <- newVariableFor . relationLeftType  . relationInfo $ rel1
  y' <- newVariableFor . relationRightType . relationInfo $ rel1

  f  <- unfoldFormula (TermApp x (TermVar x')) (TermApp y (TermVar y')) rel2
  
  addRestriction x y (relationLanguageSubset ri) (ForallPairs (x', y') rel1 f)
--  return (ForallPairs (x', y') rel1 f)

unfoldFunLabPairs :: 
    Term -> Term -> RelationInfo -> Relation -> Relation -> Unfolded Formula
unfoldFunLabPairs x y ri rel1 rel2 = do
  x' <- newVariableFor . relationLeftType  . relationInfo $ rel1
  y' <- newVariableFor . relationRightType . relationInfo $ rel1

  f  <- unfoldFormula (TermApp x (TermVar x')) (TermApp y (TermVar y')) rel2
  
-- addRestriction x y (relationLanguageSubset ri) (ForallPairs (x', y') rel1 f)
  return (ForallPairs (x', y') rel1 f)


unfoldFunVars :: 
    Term -> Term -> RelationInfo -> Relation -> Relation -> Unfolded Formula
unfoldFunVars x y ri rel1 rel2 = do
  let t1 = relationLeftType (relationInfo rel1)
  let t2 = relationRightType (relationInfo rel1)

  x' <- newVariableFor t1
  y' <- newVariableFor t2

  l  <- toggleSimplifications (unfoldFormula (TermVar x') (TermVar y') rel1)
  r  <- unfoldFormula (TermApp x (TermVar x')) (TermApp y (TermVar y')) rel2

  let f = ForallVariables x' t1 (ForallVariables y' t2 (Implication l r))
  addRestriction x y (relationLanguageSubset ri) f
--  return f


unfoldFunLabVars :: 
    Term -> Term -> RelationInfo -> Relation -> Relation -> Unfolded Formula
unfoldFunLabVars x y ri rel1 rel2 = do
  let t1 = relationLeftType (relationInfo rel1)
  let t2 = relationRightType (relationInfo rel1)

  x' <- newVariableFor t1
  y' <- newVariableFor t2

  l  <- toggleSimplifications (unfoldFormula (TermVar x') (TermVar y') rel1)
  r  <- unfoldFormula (TermApp x (TermVar x')) (TermApp y (TermVar y')) rel2

  let f = ForallVariables x' t1 (ForallVariables y' t2 (Implication l r))
  return f


addRestriction :: Term -> Term -> LanguageSubset -> Formula -> Unfolded Formula
addRestriction x y l f = do
  simple <- simplificationsAllowed
  case l of
    SubsetWithSeq EquationalTheorem -> 
      if simple
        then return f
        else let botrefl = Equivalence (Predicate (IsNotBot x))
                                       (Predicate (IsNotBot y))
              in return $ Conjunction botrefl f
    SubsetWithSeq InequationalTheorem -> 
      if simple
        then return f
        else return $ Conjunction (Implication (Predicate (IsNotBot x)) 
                                               (Predicate (IsNotBot y))) f
    otherwise -> return f





------- Unfold lifts ----------------------------------------------------------


-- | Extracts all lift relations and returns their definition.

unfoldLifts :: [ValidDeclaration] -> Intermediate -> [UnfoldedLift]  
unfoldLifts vds i =
  let decls = map rawDeclaration vds
      rs = collectLifts (intermediateRelation i)

      recUnfold done rs = let (us, ms) = unzip (map unfold rs)
                              ns = concat ms \\ (done ++ rs)
                           in if null ns
                                then us
                                else us ++ recUnfold (done ++ rs) ns
      
      unfold r = case r of 
                   RelLift ri con rs -> let (u,ms) = unfoldDecl decls ri con rs
                                         in (UnfoldedLift r u, ms)
      
      eqLift (UnfoldedLift r1 _) (UnfoldedLift r2 _) = r1 == r2
  in nubBy eqLift $ recUnfold [] rs



collectLifts :: Data a => a -> [Relation]
collectLifts = nub . listify isLift
  where
    isLift rel = case rel of
      RelLift _ _ _ -> True
      otherwise     -> False



unfoldDecl :: 
    [Declaration] -> RelationInfo -> TypeConstructor -> [Relation] 
    -> ([UnfoldedDataCon], [Relation])
unfoldDecl decls ri con rs = 
  let botPair = case relationLanguageSubset ri of
                  BasicSubset -> []
                  otherwise   -> [BotPair]
      vars t n = map (\i -> TVar (t : show i)) [1..n]
   in case con of
        ConList    -> (botPair ++ unfoldList ri (head rs), [])
        ConTuple n -> (botPair ++ [unfoldTuple n rs], [])
        otherwise  -> 
          let d = fromJust (find (isDeclOf con) decls)
           in case d of
                DataDecl d'    -> 
                  let ucs = map (unfoldCon (dataVars d') rs) (dataCons d')
                   in (botPair ++ ucs, collectLifts ucs)
                NewtypeDecl d' -> 
                  let uc = unfoldCon (newtypeVars d') rs 
                                     (DataCon (newtypeCon d') 
                                              [Unbanged (newtypeRhs d')])
                   in ([uc], collectLifts uc)
  where
    isDeclOf (Con c) d = case d of
      DataDecl _    -> getDeclarationName d == c
      NewtypeDecl _ -> getDeclarationName d == c
      otherwise     -> False



unfoldList :: RelationInfo -> Relation -> [UnfoldedDataCon]
unfoldList ri rel = 
  let x  = TVar "x"
      y  = TVar "y"
      xs = TVar "xs"
      ys = TVar "ys"
      vs = listify (\(_::TermVariable) -> True) rel
      fs = map (\(TVar v) -> v) (x:y:xs:ys:vs) 
   in [ ConPair DConEmptyList
      , ConMore DConConsList [x,xs] [y,ys]
            (Conjunction (unfoldFormulaEx fs (TermVar x, TermVar y, rel))
                         (Predicate (IsMember (TermVar xs) (TermVar ys) 
                                              (RelLift ri ConList [rel]))))
      ]


unfoldTuple :: Int -> [Relation] -> UnfoldedDataCon
unfoldTuple n rs = 
  let xs = map (\i -> TVar ('x' : show i)) [1..n]
      ys = map (\i -> TVar ('y' : show i)) [1..n]
      vs = listify (\(_::TermVariable) -> True) rs
      fs = map (\(TVar v) -> v) (xs ++ ys ++ vs)
      txs = map TermVar xs
      tys = map TermVar ys
      th = foldl1 Conjunction (map (unfoldFormulaEx fs) (zip3 txs tys rs))
   in ConMore (DConTuple n) xs ys th



unfoldCon :: 
    [TypeVariable] -> [Relation] -> DataConstructorDeclaration 
    -> UnfoldedDataCon
unfoldCon vs rs (DataCon name ts) =
  if null ts
    then ConPair (DCon (unpackIdent name))
    else let n  = length ts
             xs = map (\i -> TVar ('x' : show i)) [1..n]
             ys = map (\i -> TVar ('y' : show i)) [1..n]
             is = map (interpretEx ([], []) vs rs . withoutBang) ts
             os = listify (\(_::TermVariable) -> True) rs
             fs = map (\(TVar v) -> v) (xs ++ ys ++ os)
             txs = map TermVar xs
             tys = map TermVar ys
             th = foldl1 Conjunction (map (unfoldFormulaEx fs) 
                                          (zip3 txs tys is))
          in ConMore (DCon (unpackIdent name)) xs ys th
                              




unfoldFormulaEx :: 
    [String] -> (Term, Term, Relation) -> Formula
unfoldFormulaEx forbidden (x, y, rel) = 
  let s = UnfoldedState
          { newVariableNames = filter (`notElem` forbidden) variableNameStore
          , newFunctionNames1 = filter (`notElem` forbidden) functionNameStore1
          , newFunctionNames2 = filter (`notElem` forbidden) functionNameStore2
          }
   in runReader (evalStateT (unfoldFormula x y rel) s) (True, False)
                                                    

interpretEx :: 
    ([String], [TypeExpression]) -> [TypeVariable] -> [Relation] 
    -> TypeExpression -> Relation
interpretEx ns vs rs t = 
  let e = Map.fromList (zip vs rs)
      l = relationLanguageSubset . relationInfo . head $ rs
   in evalState (runReaderT (interpretM l t) e) ns






------- Exported functions ----------------------------------------------------


-- | Extracts all class constraints and returns their definition.

unfoldClasses :: [ValidDeclaration] -> Intermediate -> [UnfoldedClass]
unfoldClasses vds i = 
  let ds = map rawDeclaration vds
      cs = collectClasses (intermediateRelation i)
      ns = map (\(TVar n) -> n) (listify (\(_::TermVariable) -> True) cs)
      fs = signatureNames i ++ [intermediateName i] ++ ns
      rs = interpretNameStore i
      
      recUnfold done cs =
        let (us, os) = unzip (map (unfoldClass rs ds fs) cs)
            done' = done ++ cs 
            ns = concat os \\ done'
         in if null ns
              then us
              else us ++ recUnfold done' ns

   in recUnfold [] cs



collectClasses :: Data a => a -> [(Relation, TypeClass)]
collectClasses = nub . everything (++) ([] `mkQ` getCC)
  where
    getCC rel = case rel of
      RelAbs ri rv (t1,t2) res _ -> 
        let cs  = concatMap getClasses res
            ri' = ri { relationLeftType = t1
                     , relationRightType = t2 }
            r   = RelVar ri' rv
         in map (\c -> (r, c)) cs
      FunAbs ri fv (t1, t2) res _ ->
        let cs  = concatMap getClasses res
            ri' = ri { relationLeftType = t1
                     , relationRightType = t2 }
            r   = FunVar ri' (either (Left . TermVar) (Right . TermVar) fv)
         in map (\c -> (r, c)) cs
      otherwise           -> []

    getClasses r = case r of
      RespectsClasses tcs -> tcs
      otherwise           -> []



unfoldClass :: 
    ([String], [TypeExpression]) -> [Declaration] -> [String] 
    -> (Relation, TypeClass) -> (UnfoldedClass, [(Relation, TypeClass)])
unfoldClass istore decls forbiddenNames (r, c@(TC name)) =
  let ClassDecl d = fromJust (find (\d -> getDeclarationName d == name) decls)
      ri = relationInfo r

      interpretSig s = interpretEx istore [classVar d] [r] (signatureType s)
      
      methodName = TermVar . TVar . unpackIdent . signatureName
      leftMethod s = TermIns (methodName s) (relationLeftType ri)
      rightMethod s = TermIns (methodName s) (relationRightType ri)
      
      asFormula s = unfoldFormulaEx
                      forbiddenNames 
                      (leftMethod s, rightMethod s, interpretSig s)

      fs = map asFormula (classFuns d)

      ps = map (\c -> (r,c)) (superClasses d)
      ds = concatMap collectClasses fs

      v = case r of
            RelVar _ rv -> Left rv
            FunVar _ fv -> either (Right . unterm) (Right . unterm) fv
      unterm (TermVar v) = v
   
   in (UnfoldedClass (superClasses d) c v fs, ps ++ ds)




