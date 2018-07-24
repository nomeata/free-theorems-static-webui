


-- | Pretty printer for Haskell declarations.
--   It provides functions to transform declarations and especially type
--   signatures into documents.
--
--   See the module \"Text.PrettyPrint\" for more details about the used
--   document type.

module Language.Haskell.FreeTheorems.PrettyTypes where



import Text.PrettyPrint

import Language.Haskell.FreeTheorems.BasicSyntax
import Language.Haskell.FreeTheorems.PrettyBase



------- Declarations ----------------------------------------------------------


-- | Pretty-prints a declaration.

prettyDeclaration :: Declaration -> Doc
prettyDeclaration (TypeDecl decl)    = prettyTypeDeclaration decl
prettyDeclaration (DataDecl decl)    = prettyDataDeclaration decl
prettyDeclaration (NewtypeDecl decl) = prettyNewtypeDeclaration decl
prettyDeclaration (ClassDecl decl)   = prettyClassDeclaration decl
prettyDeclaration (TypeSig decl)     = prettySignature decl


instance Show Declaration where
  show = show . prettyDeclaration
  showList ds = (++) (show . vcat . map prettyDeclaration $ ds)



-- | Pretty-prints a type declaration.

prettyTypeDeclaration :: TypeDeclaration -> Doc
prettyTypeDeclaration (Type ident vs t) =
  isep 2 (
    [text "type", prettyIdentifier ident]
    ++ map prettyTypeVariable vs
    ++ [text "=", prettyTypeExpression NoParens t])

instance Show TypeDeclaration where
  show = show . prettyTypeDeclaration



-- | Pretty-prints a data declaration.

prettyDataDeclaration :: DataDeclaration -> Doc
prettyDataDeclaration (Data ident vs ds) = 
  isep 4 [ isep 2 (
             [text "data", prettyIdentifier ident]
             ++ (map prettyTypeVariable vs))
         , vcat (zipWith (<+>) (char '=' : repeat (char '|'))
                               (map prettyDataConstructorDeclaration ds))]

instance Show DataDeclaration where
  show = show . prettyDataDeclaration



-- | Pretty-prints a data constructor declaration.

prettyDataConstructorDeclaration :: DataConstructorDeclaration -> Doc
prettyDataConstructorDeclaration (DataCon ident bs) = 
  isep 2 $ [prettyIdentifier ident] ++ map prettyBangTypeExpression bs

instance Show DataConstructorDeclaration where
  show = show . prettyDataConstructorDeclaration



-- | Pretty-prints a type expression having an optional strictness flag.

prettyBangTypeExpression :: BangTypeExpression -> Doc
prettyBangTypeExpression (Banged t)   = char '!'
                                        <> prettyTypeExpression ParensFunOrCon t
prettyBangTypeExpression (Unbanged t) = prettyTypeExpression ParensFunOrCon t

instance Show BangTypeExpression where
  show = show . prettyBangTypeExpression



-- | Pretty-prints a newtype declaration.

prettyNewtypeDeclaration :: NewtypeDeclaration -> Doc
prettyNewtypeDeclaration (Newtype ident vs con t) =
  isep 2 (
    [text "newtype", prettyIdentifier ident]
    ++ map prettyTypeVariable vs
    ++ [char '=', prettyIdentifier con, prettyTypeExpression ParensFunOrCon t])

instance Show NewtypeDeclaration where
  show = show . prettyNewtypeDeclaration



-- | Pretty-prints a class declaration.

prettyClassDeclaration :: ClassDeclaration -> Doc
prettyClassDeclaration (Class scs ident tv sigs) =
  let ctx = zip scs (repeat tv)
   in isep 2 [text "class", prettyContext ctx, prettyIdentifier ident,
              prettyTypeVariable tv,
              if null sigs then empty else text "where"]
      $$ nest 4 (vcat (map prettySignature sigs))

instance Show ClassDeclaration where
  show = show . prettyClassDeclaration



-- | Pretty-prints a type signature.

prettySignature :: Signature -> Doc
prettySignature (Signature ident t) =
  isep 2 [prettyIdentifier ident, text "::", prettyTypeExpression NoParens t]

instance Show Signature where
  show = show . prettySignature



-- | Pretty-prints a class context constraining certain type variables.

prettyContext :: [(TypeClass, TypeVariable)] -> Doc
prettyContext []  = empty
prettyContext ctx =
  let prettyCV (c,v) = prettyTypeClass c <+> prettyTypeVariable v
   in fsep (
        (parensIf ((length ctx) > 1) 
                  (fsep $ punctuate comma $ map prettyCV ctx))
        : [text "=>"])



------- Type expressions ------------------------------------------------------


instance Show TypeExpression where
  showsPrec d t = 
    let p = case d of
              0         -> NoParens
              1         -> ParensFun
              otherwise -> ParensFunOrCon
     in (++) (show (prettyTypeExpression p t))



-- | Pretty-prints a type expression.

prettyTypeExpression :: Parens -> TypeExpression -> Doc

prettyTypeExpression _ (TypeVar v) = prettyTypeVariable v

prettyTypeExpression _ (TypeCon ConUnit _) = prettyTypeConstructor ConUnit

prettyTypeExpression _ (TypeCon ConList [t]) =
  brackets (prettyTypeExpression NoParens t)

    -- the following two cases are given to pretty-print also invalid
    -- type expressions, they should usually not occur
prettyTypeExpression _ (TypeCon ConList []) = prettyTypeConstructor ConList
prettyTypeExpression _ (TypeCon ConList (_:_:_)) = brackets (text "...")

prettyTypeExpression _ (TypeCon (ConTuple _) ts) = 
  parens $ fsep $ punctuate comma $ map (prettyTypeExpression NoParens) ts

prettyTypeExpression _ (TypeCon ConInt _)     = prettyTypeConstructor ConInt
prettyTypeExpression _ (TypeCon ConInteger _) = prettyTypeConstructor ConInteger
prettyTypeExpression _ (TypeCon ConFloat _)   = prettyTypeConstructor ConFloat
prettyTypeExpression _ (TypeCon ConDouble _)  = prettyTypeConstructor ConDouble
prettyTypeExpression _ (TypeCon ConChar _)    = prettyTypeConstructor ConChar

prettyTypeExpression p (TypeCon (Con ident) ts) =
  parensIf (p >= ParensFunOrCon && not (null ts)) $
    isep 2 $ (prettyIdentifier ident) 
             : (map (prettyTypeExpression ParensFunOrCon) ts)

prettyTypeExpression p (TypeFun t1 t2) =
  parensIf (p > NoParens) $ 
    fsep (zipWith (<+>) (empty : repeat (text "->")) 
                        (map (prettyTypeExpression ParensFun) (t1 : funs t2)))
  where
    funs (TypeFun t1 t2) = t1 : funs t2
    funs t               = [t]

prettyTypeExpression p (TypeFunLab t1 t2) =
  parensIf (p > NoParens) $ 
    fsep (zipWith (<+>) (empty : repeat (text "->")) 
                        (map (prettyTypeExpression ParensFun) (t1 : funs t2)))
  where
    funs (TypeFunLab t1 t2) = t1 : funs t2
    funs t                  = [t]

prettyTypeExpression p (TypeAbs v tcs t) =
  let (vs, cx, t') = collectAbstractions v tcs t
   in parensIf (p > NoParens) $
        fsep $ 
          [text "forall"] ++ (map prettyTypeVariable vs)
          ++ [char '.', prettyContext cx, prettyTypeExpression NoParens t']

prettyTypeExpression p (TypeAbsLab v tcs t) =
  let (vs, cx, t') = collectAbstractions v tcs t
   in parensIf (p > NoParens) $
        fsep $ 
          [text "forall"] ++ (map prettyTypeVariable vs)
          ++ [char '.', prettyContext cx, prettyTypeExpression NoParens t']

prettyTypeExpression p (TypeExp te) = prettyFixedTypeExpression te



-- | Collects all type abstractions which follow each other. This is used to get
--   a more compact output.

collectAbstractions :: 
    TypeVariable 
    -> [TypeClass] 
    -> TypeExpression 
    -> ([TypeVariable], [(TypeClass, TypeVariable)], TypeExpression)

collectAbstractions v tcs t =
  let cx = zip tcs (repeat v)
   in case t of
        TypeAbs v' tcs' t'    -> 
          let (vs, cx', t'') = collectAbstractions v' tcs' t'
           in (v : vs, cx ++ cx', t'')
	TypeAbsLab v' tcs' t' -> 
          let (vs, cx', t'') = collectAbstractions v' tcs' t'
           in (v : vs, cx ++ cx', t'')
         
        otherwise             -> ([v], cx, t)



-- | Pretty-prints a type constructor.

prettyTypeConstructor :: TypeConstructor -> Doc
prettyTypeConstructor ConUnit      = parens (empty)  
prettyTypeConstructor ConList      = brackets (empty)
prettyTypeConstructor (ConTuple n) =
  parens . hcat . punctuate comma . take n . repeat $ empty
prettyTypeConstructor ConInt       = text "Int"
prettyTypeConstructor ConInteger   = text "Integer"
prettyTypeConstructor ConFloat     = text "Float"
prettyTypeConstructor ConDouble    = text "Double"
prettyTypeConstructor ConChar      = text "Char"
prettyTypeConstructor (Con c)      = prettyIdentifier c 



-- | Pretty-prints a type variable.

prettyTypeVariable :: TypeVariable -> Doc
prettyTypeVariable (TV ident) = prettyIdentifier ident

instance Show TypeVariable where
  show = show . prettyTypeVariable



-- | Pretty-prints a type class.

prettyTypeClass :: TypeClass -> Doc
prettyTypeClass (TC ident) = prettyIdentifier ident

instance Show TypeClass where
  show = show . prettyTypeClass



-- | Pretty-prints a fixed type expression.

prettyFixedTypeExpression :: FixedTypeExpression -> Doc
prettyFixedTypeExpression (TF ident) = prettyIdentifier ident

instance Show FixedTypeExpression where
  show = show . prettyFixedTypeExpression



-- | Pretty-prints an identifier.

prettyIdentifier :: Identifier -> Doc
prettyIdentifier (Ident i) = text i

instance Show Identifier where
  show = show . prettyIdentifier





