


module ParserPrettyPrinterTests (tests) where



import Control.Monad (liftM, replicateM)
import Control.Monad.Writer (runWriter)
import Data.Generics (everywhere, mkT)
import Test.QuickCheck
import Text.PrettyPrint (vcat)

import Language.Haskell.FreeTheorems.Syntax
import qualified Language.Haskell.FreeTheorems.Parser.Haskell98 as Haskell98
import qualified Language.Haskell.FreeTheorems.Parser.Hsx as Hsx
import Language.Haskell.FreeTheorems.PrettyTypes

import Tests



-- | All test cases.

tests :: IO ()
tests = do
  doTest "Haskell98.parse . prettyPrint == id" prop_parsePrettyPrint_Haskell98
  doTest "Hsx.parse . prettyPrint == id" prop_parsePrettyPrint_Hsx



-- | Property: Parsing a pretty-printed declaration results in the same
--   declaration. This property is based on the Haskell98 parser.

prop_parsePrettyPrint_Haskell98 decls = 
  let (pds, es) = runWriter . Haskell98.parse 
                            . show . vcat . map prettyDeclaration $ ds
   in not (null ds) ==> (null es && not (null pds) && pds == ds)
  where
    types = decls :: ListOfDeclarations
    ds = map modifyTypeExpressions (getDeclarations decls)

    -- type expressions have to be modified because arbitrary type expressions
    -- may contain FixedTypeExpressions, explicit type abstractions and 
    -- type constructors applied to a wrong number of arguments
    modifyTypeExpressions = everywhere (mkT adjustType)

    adjustType t = case t of
      TypeCon ConUnit _       -> TypeCon ConUnit []
      TypeCon ConList []      -> TypeCon ConList [TypeCon ConUnit []]
      TypeCon ConList (x:_)   -> TypeCon ConList [x]
      TypeCon (ConTuple _) [] -> TypeCon ConUnit []
      TypeCon (ConTuple n) xs -> if length xs == 1
                                   then TypeCon ConList xs
                                   else TypeCon (ConTuple (length xs)) xs
      TypeCon ConInt _        -> TypeCon ConInt []
      TypeCon ConInteger _    -> TypeCon ConInteger []
      TypeCon ConFloat _      -> TypeCon ConFloat []
      TypeCon ConDouble _     -> TypeCon ConDouble []
      TypeCon ConChar _       -> TypeCon ConChar []
      TypeAbs _ _ t'          -> t'
      TypeExp (TF i)          -> TypeVar (TV i)
      otherwise               -> t



-- | Property: Parsing a pretty-printed declaration results in the same
--   declaration. This property is based on the Hsx parser.

prop_parsePrettyPrint_Hsx decls = 
  let (pds, es) = runWriter . Hsx.parse 
                            . show . vcat . map prettyDeclaration $ ds
   in not (null ds) ==> (null es && not (null pds) && pds == ds)
  where
    types = decls :: ListOfDeclarations
    ds = map modifyTypeExpressions (getDeclarations decls)

    -- type expressions have to be modified because arbitrary type expressions
    -- may contain FixedTypeExpressions, explicit type abstractions and 
    -- type constructors applied to a wrong number of arguments
    modifyTypeExpressions = everywhere (mkT adjustType)

    adjustType t = case t of
      TypeCon ConUnit _       -> TypeCon ConUnit []
      TypeCon ConList []      -> TypeCon ConList [TypeCon ConUnit []]
      TypeCon ConList (x:_)   -> TypeCon ConList [x]
      TypeCon (ConTuple _) [] -> TypeCon ConUnit []
      TypeCon (ConTuple n) xs -> if length xs == 1
                                   then TypeCon ConList xs
                                   else TypeCon (ConTuple (length xs)) xs
      TypeCon ConInt _        -> TypeCon ConInt []
      TypeCon ConInteger _    -> TypeCon ConInteger []
      TypeCon ConFloat _      -> TypeCon ConFloat []
      TypeCon ConDouble _     -> TypeCon ConDouble []
      TypeCon ConChar _       -> TypeCon ConChar []
      TypeAbs _ _ t'          -> t'
      TypeExp (TF i)          -> TypeVar (TV i)
      otherwise               -> t


