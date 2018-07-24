


module Language.Haskell.FreeTheorems.PrettyBase where



import Text.PrettyPrint



-- | Prints a list of documents where all documents not fitting on a line are
--   printed in following lines indented by the amount given as the first
--   argument.

isep :: Int -> [Doc] -> Doc
isep _ [] = empty
isep n (d:ds) = nest n $ fsep $ (nest (-n) d) : ds



-- | Puts parentheses around a document, if the first argument is 'True'.

parensIf :: Bool -> Doc -> Doc
parensIf putParens = if putParens then parens else id



-- | A data type to describe around which type expressions parentheses are to be
--   put.

data Parens
  = NoParens        -- ^ Don't put any parentheses.
  | ParensFun       -- ^ The type expression occurs as an argument to a
                    --   function.
  | ParensFunOrCon  -- ^ The type expression occurs as an argument to a
                    --   function, type constructor or type class.
  deriving (Eq, Ord)



-- | Returns a document when a condition holds. Otherwise, the empty document
--   is returned.

when :: Bool -> Doc -> Doc
when False = const empty
when True  = id



-- | Returns a list of documents when a condition holds. Otherwise, the empty
--   list is returned.

whenL :: Bool -> [Doc] -> [Doc]
whenL False = const []
whenL True  = id


