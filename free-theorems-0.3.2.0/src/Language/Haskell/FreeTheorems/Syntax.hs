


-- | Declars data types describing the abstract syntax of a subset of Haskell
--   in the FreeTheorems library. Only declarations and type expressions are
--   covered by these data types.
--
--   Note that the data types of this module do not reflect Haskell98.
--   This is because they are able to express higher-rank functions which are
--   not part of Haskell98.
--   Also, in type expressions, a type variable must not be applied to any type
--   expression. Thus, for example, the type @m a@, as occuring in the functions
--   of the @Monad@ type class, is not expressable.
--   The reason for this restriction is that the FreeTheorems library cannot
--   handle such types.

module Language.Haskell.FreeTheorems.Syntax (

    -- * Declarations

    Declaration (..)
  , getDeclarationName
  , getDeclarationArity
  , DataDeclaration (..)
  , NewtypeDeclaration (..)
  , TypeDeclaration (..)
  , ClassDeclaration (..)
  , Signature (..)
  , DataConstructorDeclaration (..)
  , BangTypeExpression (..)
  

    -- * Type expressions

  , TypeExpression (..)
  , TypeConstructor (..)
  , TypeClass (..)
  , TypeVariable (..)
  , FixedTypeExpression (..)


    -- * Identifiers

  , Identifier (..)

) where



import Language.Haskell.FreeTheorems.BasicSyntax
import Language.Haskell.FreeTheorems.ValidSyntax
import Language.Haskell.FreeTheorems.PrettyTypes


