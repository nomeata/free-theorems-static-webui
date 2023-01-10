{-# LANGUAGE FlexibleContexts #-}


-- | Provides error handling functions for checking parser output.
--   The functions and data types of this module are mostly tiny, little
--   helpers used by all parser modules.

module Language.Haskell.FreeTheorems.Frontend.Error where



import Control.Monad (foldM)
import Control.Monad.Error (Error(..), throwError)
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.List (intersperse)
import Text.PrettyPrint (Doc, empty, text, fsep, ($$), nest)

import Language.Haskell.FreeTheorems.Syntax
    (Declaration, getDeclarationName, unpackIdent)



-- | A wrapper type for a @Writer@ which stores pretty-printable documents along
--   with checked values.

type Checked a = Writer [Doc] a



-- | A wrapper type for @Writer@ which stores pretty-printable documents along
--   with parsed values.
--   This type is provided as standard return type for parsers.

type Parsed a = Writer [Doc] a





-- | The error type is just a synonym for @Either@ where errors are represented
--   by a pretty-printable @Doc@.

type ErrorOr a = Either Doc a

-- needed to make 'ErrorOr' a monad
instance Error Doc where
  noMsg    = empty
  strMsg s = text s



-- | A wrapper function for @runWriter@.

runChecks :: Checked a -> (a, [Doc])
runChecks = runWriter



-- | Applies a checking function (the first argument) element-wise to a list of
--   values (the second argument). The result list contains only those elements
--   for which the checking function does not yield an error.

foldChecks :: (a -> ErrorOr b) -> [a] -> Checked [a]
foldChecks check = foldM doCheck []
  where
    doCheck xs x = 
      case getError (check x) of
        Nothing -> return (xs ++ [x])
        Just e  -> tell [e] >> return xs



-- | Checks if the argument contains an error.

isError :: ErrorOr a -> Bool
isError = either (const True) (const False)



-- | Returns the error message stored in the argument or @Nothing@ if there is 
--   no error message in the argument.

getError :: ErrorOr a -> Maybe Doc
getError = either Just (const Nothing)



-- | If the first argument is True, then the second argument is taken as an
--   error message. Otherwise () is returned as a non-error message.

errorIf :: Bool -> Doc -> ErrorOr ()
errorIf False = return . const ()
errorIf True  = throwError



-- | Transforms a string into a pretty-printed document by splitting the string
--   into words and forming a pretty paragraph of all words.

pp :: String -> Doc
pp = fsep . map text . words



-- | Checks a declaration for errors.
--   If the second argument is an error, this function extends the error 
--   message to make clear it belongs to a declaration.

inDecl :: Declaration -> ErrorOr a -> ErrorOr a
inDecl d e = case getError e of
  Nothing  -> e
  Just doc -> throwError $
                pp ("In the declaration of " 
                    ++ unpackIdent (getDeclarationName d) ++ ":")
                $$ nest 2 doc
    


-- | Used to extend error messages by a list of items violating a certain rule. 

violating :: String -> [String] -> String
violating name xs =
  let text = if length xs == 1
               then " The following " ++ name ++ " violates this rule: "
               else " The following " ++ name ++ "s violate this rule: "
   in text ++ (concat . intersperse ", " $ xs)




