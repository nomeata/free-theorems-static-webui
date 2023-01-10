


-- | Data structures and functions to automatically generate free theorems.
--
--   This library is based on the following papers:
--
--   * /Theorems For Free!/, Philip Wadler, in Functional Programming Languages
--     and Computer Architecture Proceedings, 1989.
--     <http://homepages.inf.ed.ac.uk/wadler/papers/free/free.ps>
--
--   * /The Impact of seq on Free Theorems-Based Program Transformations/,
--     Patricia Johann and Janis Voigtl&#xE4;nder, Fundamenta Informaticae,
--     2006. <http://www.orchid.inf.tu-dresden.de/~voigt/seqFinal.pdf>
--
--
--   The intended usage of this library is as follows.
--   
--   (1) Parse a list of declarations using one of two parsers 
--       ('Language.Haskell.FreeTheorems.Parser.Haskell98.parse' or 
--       'Language.Haskell.FreeTheorems.Parser.Hsx.parse') or any other
--       suitable parser.
--       Use 'check' to obtain a list of valid declarations.
--
--   (2) Optional:
--       Parse more declarations and validate them against the previously 
--       loaded list of valid declarations with 'checkAgainst'.
--
--   (3) Extract all valid signatures from a list of valid declarations by
--       'filterSignatures'.
--
--   (4) Interpret a signature ('interpret'), transform it to a theorem
--       ('asTheorem') and pretty-print it ('prettyTheorem').
--
--   (5) Optional: Specialise relation variables to functions 
--       ('relationVariables' and 'specialise').
--
--   (6) Optional: Extract lifted relations to show their definition
--       ('unfoldLifts') and pretty-print them ('prettyUnfoldedLift').
--
--   (7) Optional: Extract class constraints to show their definition
--       ('unfoldClasses') and pretty-print them ('prettyUnfoldedClass').
--
--   (8) Optional: Further simplify the Formulas ('simplify') or UnfoldedLift
--       ('simplifyUnfoldedLift') by syntactic transformations.

module Language.Haskell.FreeTheorems (

    -- * Valid declarations

    -- $restrictions

    ValidDeclaration
  , ValidSignature
  , rawDeclaration
  , rawSignature
  , filterSignatures

    
    -- * Manufacturing valid declarations 
    
  , Parsed
  , Checked
  , runChecks
  , check
  , checkAgainst

    
    -- * Generating free theorems

  , LanguageSubset (..)
  , TheoremType (..)
  , Intermediate
  , interpret
  , asTheorem
  , asCompleteTheorem
  , relationVariables
  , specialise
  , specialiseInverse
  , unfoldLifts
  , unfoldClasses

    -- * Simplifications
    --
    -- | These syntactic transformations are only valid for equational theorems
    --   in the basic subset or the subset with fix, as eta reduction will be tried.

  , simplify
  , simplifyUnfoldedLift

    -- * Pretty printing
    
    -- | The pretty printer is based on the module \"Text.PrettyPrint\" which
    --   is usually implemented by \"Text.PrettyPrint.HughesPJ\". See there for
    --   information on how to modify documents.

  , PrettyTheoremOption (..)
  , prettyDeclaration
  , prettySignature
  , prettyTheorem
  , prettyRelationVariable
  , prettyUnfoldedLift
  , prettyUnfoldedClass

) where



import Text.PrettyPrint (Doc, empty)

import Language.Haskell.FreeTheorems.BasicSyntax
import Language.Haskell.FreeTheorems.ValidSyntax
import Language.Haskell.FreeTheorems.Frontend
import Language.Haskell.FreeTheorems.LanguageSubsets
import Language.Haskell.FreeTheorems.Intermediate
import Language.Haskell.FreeTheorems.Theorems
import Language.Haskell.FreeTheorems.Theorems.Simplify
import Language.Haskell.FreeTheorems.Unfold
import Language.Haskell.FreeTheorems.PrettyTypes
import Language.Haskell.FreeTheorems.PrettyTheorems






-- $restrictions
--
--   The restrictions on valid declarations and valid type signatures, above
--   what is already ensured by the stucture of declarations (see 
--   "Language.Haskell.FreeTheorems.Syntax"), are as follows:
--
--   For @data@ and @newtype@ declarations:
--
--   * The declared type constructor is not a primitive type, i.e. it is not
--     equal to @Int@, @Integer@, @Float@, @Double@ nor @Char@.
--
--   * The variables occurring on the right-hand side have to be mentioned on
--     the left-hand side, and the left-hand side variables are pairwise
--     distinct.
--   
--   * There is at least one data constructor in the declaration of an
--     algebraic data type.
--
--   * The declaration is not nested, i.e. if the declared type constructor
--     occurs on the right-hand side, it has only type variables as arguments.
--
--   * No 'Language.Haskell.FreeTheorems.Syntax.FixedTypeExpression' occurs
--     in any type expression on the right-hand side.
--
--   * After replacing all type synonyms: No function type constructor and no
--     type abstraction occurs on the right-hand side.
--
--   For @type@ declarations:
--
--   * The declared type constructor is not a primitive type, i.e. it is not
--     equal to @Int@, @Integer@, @Float@, @Double@ nor @Char@.
--
--   * The variables occurring on the right-hand side have to be mentioned on
--     the left-hand side, and the left-hand side variables are pairwise
--     distinct.
--
--   * The declaration is not recursive, i.e. if the declared type constructor
--     occurs nowhere on the right-hand side.
--
--   * There is no group of @type@ declarations which are mutually recursive.
--
--   * No 'Language.Haskell.FreeTheorems.Syntax.FixedTypeExpression' occurs
--     in the type expression on the right-hand side.
--   
--   For @class@ declarations:
--
--   * The declared type class does not equal a primitive type.
--   
--   * The names of the class methods are pairwise distinct. 
--   
--   * The class variable occurs in the type expression of every class method.
--   
--   * The name of the class does not occur in a type expression of any class
--     method.
--   
--   * No 'Language.Haskell.FreeTheorems.Syntax.FixedTypeExpression' occurs
--     in a type expression of any class method.
--
--   * The type class hierarchy is acyclic.
--
--   For type signatures:
--   
--   * No 'Language.Haskell.FreeTheorems.Syntax.FixedTypeExpression' occurs
--     in the type expression of a signature.
--
--   Additionally, the following global restrictions need to hold:
--   
--   * There may be at most one declaration only for every name.
--
--   * Every type class occurring in any type expression is declared.
--
--   * Every type constructor occurring in any type expression is declared.
--     Furthermore, the number of arguments to every type constructor has to
--     match the number of type variables the given on the left-hand side of the
--     declaration of that type constructor.
--
--   Type synonyms do not occur in type expressions of valid declarations.
--   Every type expression of a valid declaration is closed. A special case are
--   class methods. Their types have the class variable as the only free type
--   variable.


