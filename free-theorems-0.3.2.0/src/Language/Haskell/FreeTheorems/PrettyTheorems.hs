


-- | Pretty printer for theorems.
--   It provides functions to transform theorems into documents.
--
--   See the module \"Text.PrettyPrint\" for more details about the used
--   document type.

module Language.Haskell.FreeTheorems.PrettyTheorems (
    PrettyTheoremOption (..)
  , prettyTheorem
  , prettyRelationVariable
  , prettyUnfoldedLift
  , prettyUnfoldedClass
) where

import Prelude hiding ((<>))

import Data.List (partition, find)
import Data.Maybe (mapMaybe)
import Text.PrettyPrint

import Language.Haskell.FreeTheorems.Syntax
import Language.Haskell.FreeTheorems.LanguageSubsets
import Language.Haskell.FreeTheorems.Theorems
import Language.Haskell.FreeTheorems.PrettyBase
import Language.Haskell.FreeTheorems.PrettyTypes



------- Options ---------------------------------------------------------------


-- | Possible options for pretty-printing theorems.

data PrettyTheoremOption
  = OmitTypeInstantiations      
        -- ^ Omits all instantiations of types. This option makes theorems 
        --   usually better readable.
  
  | OmitLanguageSubsets
        -- ^ Omit mentioning language subsets explicitly for certain relations.

  deriving Eq



------- Pretty control data ---------------------------------------------------


data PrettyControl = PrettyControl
  { options     :: [PrettyTheoremOption]
  , parentheses :: Parens
  , inPremise   :: Bool
  }


defaultPrettyControl :: [PrettyTheoremOption] -> PrettyControl
defaultPrettyControl opts = 
  PrettyControl
    { options = opts
    , parentheses = NoParens
    , inPremise = False
    }


withTypeInstantiations :: PrettyControl -> Bool
withTypeInstantiations = notElem OmitTypeInstantiations . options


withLanguageSubsets :: PrettyControl -> Bool
withLanguageSubsets = notElem OmitLanguageSubsets . options


noParens :: PrettyControl -> PrettyControl
noParens pc = pc { parentheses = NoParens }


useParens :: PrettyControl -> PrettyControl
useParens pc = pc { parentheses = ParensFun }


withParens :: PrettyControl -> Bool
withParens pc = parentheses pc > NoParens


setPremise :: PrettyControl -> PrettyControl
setPremise pc = pc { inPremise = not (inPremise pc) }





------- Language subsets ------------------------------------------------------


-- | Pretty-prints a language subset.

prettyLanguageSubset :: LanguageSubset -> Doc
prettyLanguageSubset l = case l of
  BasicSubset                       -> text "basic"
  SubsetWithFix EquationalTheorem   -> text "fix" <> comma <> text "="
  SubsetWithFix InequationalTheorem -> text "fix" <> comma <> text "[="
  SubsetWithSeq EquationalTheorem   -> text "seq" <> comma <> text "="
  SubsetWithSeq InequationalTheorem -> text "seq" <> comma <> text "[="





------- Formulas --------------------------------------------------------------


-- | Pretty-prints a theorem.

prettyTheorem :: [PrettyTheoremOption] -> Theorem -> Doc
prettyTheorem opt = prettyFormula (defaultPrettyControl opt)



-- | Pretty-prints a formula.

prettyFormula :: PrettyControl -> Formula -> Doc
prettyFormula pc (ForallRelations v (t1,t2) res f) =
  let rv = prettyRelationVariable v
      ts = prettyTypeExpression NoParens t1 <> comma 
           <> prettyTypeExpression NoParens t2
      cs = getTypeClasses res
      ds = if null cs
             then empty
             else parens . fsep . punctuate comma . map prettyTypeClass $ cs
   in parensIf (withParens pc) $ 
        sep 
          [ fsep $
              [ text "forall"
              , ts, text "in", text "TYPES" <> ds <> comma
              , rv, text "in"
              , text "REL" <> parens ts
                 <> if null res then char '.' else comma ]
              ++ prettyRestrictionList rv res
          , nest 1 (prettyFormula (noParens pc) f) ]

prettyFormula pc (ForallFunctions v (t1,t2) res f) =
  let ts = prettyTypeExpression NoParens t1 <> comma 
           <> prettyTypeExpression NoParens t2
      pv = either prettyTermVariable prettyTermVariable v
      cs = getTypeClasses res
      ds = if null cs
             then empty
             else parens . fsep . punctuate comma . map prettyTypeClass $ cs
   in parensIf (withParens pc) $ 
        sep 
          [ fsep $
              [ text "forall"
              , ts, text "in", text "TYPES" <> ds <> comma 
              , pv, text "::"
              , prettyTypeExpression NoParens 
                (either (\_ -> TypeFun t1 t2) (\_ -> TypeFun t2 t1) v)
                 <> if null res then char '.' else comma ]
              ++ prettyRestrictionList pv res
          , nest 1 (prettyFormula (noParens pc) f) ]

prettyFormula pc (ForallPairs (v1,v2) r f) =
  parensIf (withParens pc) $
    sep [ fsep [ text "forall"
               , parens (prettyTermVariable v1 <> comma 
                         <+> prettyTermVariable v2)
               , text "in", prettyRelation (useParens pc) False r <> char '.' ]
        , nest 1 (prettyFormula (noParens pc) f) ]

prettyFormula pc (ForallVariables v t f) =
  parensIf (withParens pc) $
    sep [ fsep [ text "forall", prettyTermVariable v, text "::"
               , prettyTypeExpression NoParens t <> char '.' ]
        , nest 1 (prettyFormula (noParens pc) f) ]

prettyFormula pc (Equivalence f1 f2) =
  parensIf (withParens pc) $
    sep [ prettyFormula (useParens pc) f1
        , text "<=>" <+> prettyFormula (useParens pc) f2]

prettyFormula pc (Implication f1 f2) =
  parensIf (withParens pc) $
    sep [ prettyFormula (useParens (setPremise pc)) f1
        , text "==>" <+> prettyFormula (useParens pc) f2]

prettyFormula pc (Conjunction f1 f2) =
  parensIf (withParens pc) $
    sep [ prettyFormula (useParens pc) f1
        , text "&&" <+> prettyFormula (useParens pc) f2]

prettyFormula pc (Predicate predicate) = 
  parensIf (withParens pc) (prettyPredicate (noParens pc) predicate)



-- | Returns the type classes of a restriction list.

getTypeClasses :: [Restriction] -> [TypeClass]
getTypeClasses = concatMap exTC
  where exTC r = case r of
          RespectsClasses tcs -> tcs
          otherwise           -> []



-- | Pretty-prints a list of restrictions.

prettyRestrictionList :: Doc -> [Restriction] -> [Doc]
prettyRestrictionList v res = case res of
  []         -> []
  (r:[])     -> v : [ prettyRestriction r <> char '.' ]
  (r1:r2:[]) -> v : (punctuate comma [prettyRestriction r1] ++ [text "and", prettyRestriction r2 <> char '.' ])
  otherwise  -> let dres = map prettyRestriction res
                 in v : (punctuate comma (init dres ++ [text "and"]) 
                        ++ [last dres <> char '.' ])



-- | Pretty-prints a restriction.

prettyRestriction :: Restriction -> Doc
prettyRestriction Strict           = text "strict"
prettyRestriction Continuous       = text "continuous"
prettyRestriction Total            = text "total"
prettyRestriction BottomReflecting = text "bottom-reflecting"
prettyRestriction LeftClosed       = text "left-closed"
prettyRestriction (RespectsClasses tcs) =
  when (not (null tcs)) $
    fsep [ text "respects"
         , parensIf (length tcs > 1) $
             fsep . punctuate comma . map prettyTypeClass $ tcs ]



-- | Pretty-prints a predicate.

prettyPredicate :: PrettyControl -> Predicate -> Doc
prettyPredicate pc (IsMember x y r) =
  fsep [ parens (prettyTerm (noParens pc) x <> comma 
                 <+> prettyTerm (noParens pc) y)
       , text "in", prettyRelation (useParens pc) False r ]

prettyPredicate pc (IsEqual x y) = 
  fsep [ prettyTerm (noParens pc) x, char '=', prettyTerm (noParens pc) y ]

prettyPredicate pc (IsLessEq x y) = 
  fsep [ prettyTerm (noParens pc) x, text "[=", prettyTerm (noParens pc) y ]

prettyPredicate pc (IsNotBot x) = 
  parensIf (withParens pc) $
    fsep [ prettyTerm (noParens pc) x, text "/=", text "_|_" ]

prettyPredicate pc (IsTrue) = 
  text "True"



-- | Pretty-prints a term.

prettyTerm :: PrettyControl -> Term -> Doc
prettyTerm pc (TermVar v) = prettyTermVariable v

prettyTerm pc (TermApp t1 t2) = 
  parensIf (withParens pc) $ prettyTerm (noParens pc) t1 <+> prettyTerm (useParens pc) t2

prettyTerm pc (TermIns t ty) =
  let d = prettyTypeExpression NoParens ty
      withTypes = withTypeInstantiations pc
      p = if withTypes then useParens else noParens
      pt = prettyTerm (useParens pc) t 
   in pt <> showInstantiation withTypes d

prettyTerm pc (TermComp []) = 
  text "id"

prettyTerm pc (TermComp [t]) = 
  parensIf (withParens pc) $ prettyTerm (noParens pc) t

prettyTerm pc (TermComp (t:ts)) = 
  parensIf (withParens pc) $ prettyTerm (noParens pc) t <+> text "." <+>
                             prettyTerm (noParens pc) (TermComp ts)



-- | Shows an instantiation (by a type).

showInstantiation :: Bool -> Doc -> Doc
showInstantiation False _ = empty
showInstantiation True  d = char '_' <> braces d


-- | Pretty-prints a term variable.

prettyTermVariable :: TermVariable -> Doc
prettyTermVariable (TVar v) = text v



------- Relations -------------------------------------------------------------


-- | Pretty-prints a relation.

prettyRelation :: PrettyControl -> Bool -> Relation -> Doc
prettyRelation _ _ (RelVar _ rv) = prettyRelationVariable rv

prettyRelation pc _ (FunVar ri (Left t)) = 
  case theoremType (relationLanguageSubset ri) of 
    EquationalTheorem   -> prettyTerm (noParens pc) t
    InequationalTheorem -> prettyTerm (useParens pc) t <> text " ; [="

prettyRelation pc _ (FunVar _ (Right t)) = 
  text "[= ; " <> prettyTerm (useParens pc) t <> text "^{-1}"

prettyRelation _ _ (RelBasic ri) = 
  case theoremType (relationLanguageSubset ri) of
    EquationalTheorem   -> text "id"
    InequationalTheorem -> text "[="

prettyRelation pc omitOrder (RelLift ri con rs) =
  let pl = case relationLanguageSubset ri of
             BasicSubset -> text "lift"
             otherwise   -> case theoremType (relationLanguageSubset ri) of
                              EquationalTheorem   -> text "lift"
                              InequationalTheorem -> if omitOrder
                                                       then text "lift"
                                                       else text "[= ; lift"
   in pl <> braces (prettyTypeConstructor con)
         <> (parens . foldl1 (\a b -> a <> comma <> b)  
                    . map (prettyRelation (noParens pc) False) $ rs)
--         <> (parens . fsep . punctuate comma 
--                           . map (prettyRelation (noParens pc) False) $ rs)


prettyRelation pc _ (RelFun ri r1 r2) = 
  let l = if withLanguageSubsets pc
            then case relationLanguageSubset ri of
                   SubsetWithSeq _ -> text "^" <> braces (prettyLanguageSubset 
                                                  (relationLanguageSubset ri))
                   otherwise       -> empty
            else empty
   in parensIf (withParens pc) $
        fsep [ prettyRelation (useParens pc) False r1
             , text "->" <> l
             , prettyRelation (useParens pc) False r2 ]

-- second function relation only used in the equational setting with Seq
prettyRelation pc _ (RelFunLab ri r1 r2) = 
   parensIf (withParens pc) $
      fsep [ prettyRelation (useParens pc) False r1
           , text "->^o" <> empty
           , prettyRelation (useParens pc) False r2 ]

prettyRelation pc _ (RelAbs ri v _ res r) = 
  let tcs = getTypeClasses res
      dcs = if null tcs
              then empty
              else parens (fcat . punctuate comma . map prettyTypeClass $ tcs)
   in parensIf (withParens pc) $
        fsep [ text "forall"
             , prettyRelationVariable v
             , text "in"
             , text "REL" 
                <> (when (withLanguageSubsets pc) $
                     text "^" <> braces (prettyLanguageSubset 
                                          (relationLanguageSubset ri)))
                <> dcs
                <> char '.'
             , prettyRelation (useParens pc) False r ]

prettyRelation pc _ (FunAbs ri v _ res r) =
  let tcs = getTypeClasses res
      dcs = if null tcs
              then empty
              else parens (fcat . punctuate comma . map prettyTypeClass $ tcs)
   in parensIf (withParens pc) $
        fsep [ text "forall"
             , either prettyTermVariable prettyTermVariable v
             , text "in"
             , either (const (text "FUN")) (const (text "FUN_i")) v
                <> (when (withLanguageSubsets pc) $
                     text "^" <> braces (prettyLanguageSubset 
                                          (relationLanguageSubset ri)))
                <> dcs
                <> char '.'
             , prettyRelation (useParens pc) False r ]





-- | Pretty-prints a relation variable.

prettyRelationVariable :: RelationVariable -> Doc
prettyRelationVariable (RVar r) = text r





------- Unfolded formulas -----------------------------------------------------


-- | Pretty-prints an unfolded lift relation.

prettyUnfoldedLift :: [PrettyTheoremOption] -> UnfoldedLift -> Doc
prettyUnfoldedLift opt (UnfoldedLift r dcs) =
  let pc = defaultPrettyControl opt
      sc = braces . fsep . punctuate comma . map (prettyUnfoldedDataCon pc) 
           $ simpleCons
      ccs = map (braces . prettyUnfoldedDataCon pc) complexCons
      dcs = if null simpleCons then ccs else sc : ccs
   in vcat $
        [ prettyRelation (noParens pc) True r ]
        ++ zipWith (\t d -> nest 2 (text t <+> d)) ("=" : repeat "u") dcs
  where
    (simpleCons, complexCons) = partition isSimpleCon dcs

    isSimpleCon d = case d of
      BotPair   -> True
      ConPair _ -> True
      otherwise -> False



-- | Pretty-prints an unfolded data constructor declaration.

prettyUnfoldedDataCon :: PrettyControl -> UnfoldedDataCon -> Doc
prettyUnfoldedDataCon _ BotPair = 
  parens (fsep (punctuate comma [ text "_|_", text "_|_" ]))

prettyUnfoldedDataCon _ (ConPair d) =
  let d' = prettyDataConstructor d []
   in parens (fsep (punctuate comma [ d', d' ]))

prettyUnfoldedDataCon pc (ConMore d xs ys f) = 
  let d1 = prettyDataConstructor d xs
      d2 = prettyDataConstructor d ys
   in sep [ fsep [ parens . fsep . punctuate comma $ [d1, d2] 
                 , text "|" ]
          , nest 2 (prettyFormula pc f) ]



-- | Pretty-prints a data constructor.

prettyDataConstructor :: DataConstructor -> [TermVariable] -> Doc
prettyDataConstructor DConEmptyList _    = brackets empty
prettyDataConstructor DConConsList [x,y] = fsep [prettyTermVariable x, text ":"
                                                , prettyTermVariable y]
prettyDataConstructor DConConsList _     = brackets empty
prettyDataConstructor (DConTuple _) xs = 
  parens (fsep . punctuate comma . map prettyTermVariable $ xs)
prettyDataConstructor (DCon s) xs = fsep (text s : map prettyTermVariable xs)



-- | Pretty-prints an unfolded type class.

prettyUnfoldedClass :: [PrettyTheoremOption] -> UnfoldedClass -> Doc
prettyUnfoldedClass opt (UnfoldedClass tcs tc v fs) =
  let pc = defaultPrettyControl opt
      pv = either prettyRelationVariable prettyTermVariable v 
      intro = [ pv, text "respects", prettyTypeClass tc ] 
   in if null tcs && null fs
        then fsep $ intro ++ (map text . words $
                      "without further restrictions")
        else vcat $
               (fsep $
                  intro ++ [text "if"]
                  ++ if null tcs
                       then []
                       else [ pv, text "respects" ]
                            ++ (punctuate comma . map prettyTypeClass $ tcs)
                  ++ if not (null tcs) && not (null fs)
                       then [ text "and" ]
                       else [])
               : (map (nest 2 . prettyFormula pc) fs)




