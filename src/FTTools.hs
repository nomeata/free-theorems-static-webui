{-# LANGUAGE TypeSynonymInstances #-}
module FTTools
   ( parseTypeString
   , specialiseAll
   , specialiseAllInverse
   , isInequational
   , parseDeclarations
   , rawFunctionName
   , rawDeclarationName
   , filterDataDeclarations
   , filterTypeDeclarations
   , filterClassDeclarations
   )
where

import Language.Haskell.FreeTheorems
import Language.Haskell.FreeTheorems.Theorems (Theorem, UnfoldedLift, UnfoldedClass)
--import Language.Haskell.FreeTheorems.Parser.Hsx (parse)
import Language.Haskell.FreeTheorems.Parser.Haskell98 (parse)
import Language.Haskell.FreeTheorems.BasicSyntax
   ( signatureName
   , unpackIdent
   , getDeclarationName
   , Declaration (DataDecl, TypeDecl, ClassDecl) -- for the "filter" functions
   )

import Data.List (find, isInfixOf, foldl')


parseDeclarations :: [ValidDeclaration] -> String -> Either String [ValidDeclaration]
parseDeclarations oldDecls text =
   let (decls, errors) = runChecks (parse text >>= checkAgainst oldDecls)
   in case errors of
      (e:_) -> Left (show e)
      []    -> Right decls


specialiseAll :: Intermediate -> Intermediate
specialiseAll im = foldl' specialise im $ relationVariables im

specialiseAllInverse :: Intermediate -> Intermediate
specialiseAllInverse im = foldl' specialiseInverse im $ relationVariables im

isInequational :: LanguageSubset -> Bool
isInequational (SubsetWithFix InequationalTheorem) = True
isInequational (SubsetWithSeq InequationalTheorem) = True
isInequational _ = False


instance Eq (ValidDeclaration) where
   x == y = rawDeclaration x == rawDeclaration y

instance Show (ValidDeclaration) where
   show = show . prettyDeclaration . rawDeclaration

instance Show (ValidSignature) where
   show = show . prettySignature . rawSignature

instance Show (Theorem) where
   show = show . prettyTheorem []

instance Show (UnfoldedLift) where
   show = show . prettyUnfoldedLift []

instance Show (UnfoldedClass) where
   show = show . prettyUnfoldedClass []


{- From FTBase.hs -}

-- Parses a type string and returns the named type obtained from parsing or an
-- error if no type was found. The function works as follows:
--
--   * If the input contains "::", then it is parsed as a named type.
--
--   * If the input is only one word, the function tries to find a type with
--     that name in the list of predefined types. If it can be found, that type
--     is parsed as a named type.
--
--   * Otherwise the input is parsed as a type without name, while a new name is
--     generated.

parseTypeString :: [ValidDeclaration] -> String -> Either String ValidSignature

parseTypeString oldDecls input | containsTwoColons input =
      parseNamedType oldDecls input

parseTypeString oldDecls input | isOneWord input =
      case find ((input==) . rawFunctionName) knownSignatures of
         Just vsig -> Right vsig
         Nothing   -> parseType oldDecls input
   where knownSignatures = filterSignatures oldDecls

parseTypeString oldDecls input =
      parseType oldDecls input


parseType :: [ValidDeclaration] -> String -> Either String ValidSignature
parseType oldDecls s = parseNamedType oldDecls ("f::"++s)

parseNamedType :: [ValidDeclaration] -> String -> Either String ValidSignature
parseNamedType oldDecls s = do
   vs <- parseDeclarations oldDecls s
   case filterSignatures vs of
      [sig] -> Right sig
      _     -> Left "no valid type signature"


containsTwoColons = isInfixOf "::"

isOneWord = (1==) . length . words

rawFunctionName :: ValidSignature -> String
rawFunctionName = unpackIdent . signatureName . rawSignature

rawDeclarationName :: ValidDeclaration -> String
rawDeclarationName = unpackIdent . getDeclarationName . rawDeclaration


filterDataDeclarations = filter $ \vd ->
   case rawDeclaration vd of
      DataDecl _ -> True
      _ -> False

filterTypeDeclarations = filter $ \vd ->
   case rawDeclaration vd of
      TypeDecl _ -> True
      _ -> False

filterClassDeclarations = filter $ \vd ->
   case rawDeclaration vd of
      ClassDecl _ -> True
      _ -> False
