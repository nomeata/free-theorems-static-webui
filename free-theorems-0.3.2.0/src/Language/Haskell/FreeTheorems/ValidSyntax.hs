


-- | Declares data types which describe valid declarations and valid type 
--   signatures. A declaration or type signature is valid when all checks (see
--   "Language.Haskell.FreeTheorems.Frontend") were passed successfully.

module Language.Haskell.FreeTheorems.ValidSyntax where



import Data.Generics (Typeable, Data)
import Data.Maybe (mapMaybe)

import Language.Haskell.FreeTheorems.BasicSyntax



-- | Marks a valid declaration.

data ValidDeclaration = ValidDeclaration 
  { rawDeclaration :: Declaration 
        -- ^ Returns the declaration structure hidden in a valid declaration.

  , isStrictDeclaration :: Bool
        -- ^ Indicates whether the declarations declares or depends on an 
        --   algebraic data type with strictness flag.
  }



-- | Marks a valid type signature.

newtype ValidSignature = ValidSignature 
  { rawSignature :: Signature
        -- ^ Returns the signature structure hidden in a valid type signature.
  }



-- | Extracts all type signatures from a list of declarations.

filterSignatures :: [ValidDeclaration] -> [ValidSignature]
filterSignatures = mapMaybe asSignature
  where 
    asSignature (ValidDeclaration decl _) = 
      case decl of
        TypeSig sig -> Just (ValidSignature sig)
        otherwise   -> Nothing



