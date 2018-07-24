{-# LANGUAGE DeriveDataTypeable #-}


-- | Declares the basic syntax of a Haskell98 subset enriched with 
--   higher-ranked functions. Additionally, it defines small convenience
--   functions. 

module Language.Haskell.FreeTheorems.BasicSyntax where



import Data.Generics (Typeable, Data)



-- | A Haskell declaration which corresponds to a @type@, @data@, @newtype@,
--   @class@ or type signature declaration.
--
--   In type expressions, type variables must not be applied to type
--   expressions. Thus, for example, the functions of the @Monad@ class are not
--   expressible.
--   However, in extension to Haskell98, higher-rank types can be expressed.
--   
--   This data type does not reflect all information of a declaration. Only the
--   aspects needed by the FreeTheorems library are covered.

data Declaration
  = TypeDecl TypeDeclaration            -- ^ A @type@ declaration.
  | DataDecl DataDeclaration            -- ^ A @data@ declaration.
  | NewtypeDecl NewtypeDeclaration      -- ^ A @newtype@ declaration.
  | ClassDecl ClassDeclaration          -- ^ A @class@ declaration.
  | TypeSig Signature                   -- ^ A type signature.
  deriving (Eq, Typeable, Data)



-- | Gets the name of the item declared by a declaration.
--   This is the type constructor for @data@, @newtype@ and @type@ declarations,
--   the name of a class for a @class@ declaration or the name of a type
--   signature.

getDeclarationName :: Declaration -> Identifier
getDeclarationName (DataDecl d)    = dataName d
getDeclarationName (NewtypeDecl d) = newtypeName d
getDeclarationName (TypeDecl d)    = typeName d
getDeclarationName (ClassDecl d)   = className d
getDeclarationName (TypeSig s)     = signatureName s



-- | Gets the arity of a type constructor or @Nothing@ if this is not a
--   @data@, @newtype@ or @type@ declaration.

getDeclarationArity :: Declaration -> Maybe Int
getDeclarationArity (DataDecl d)    = Just . length . dataVars $ d
getDeclarationArity (NewtypeDecl d) = Just . length . newtypeVars $ d
getDeclarationArity (TypeDecl d)    = Just . length . typeVars $ d
getDeclarationArity (ClassDecl d)   = Nothing
getDeclarationArity (TypeSig s)     = Nothing



-- | A @type@ declaration for a type synonym.

data TypeDeclaration = Type 
  { typeName :: Identifier     -- ^ The type constructor name.
  , typeVars :: [TypeVariable] -- ^ The type variables on the left-hand side.
  , typeRhs  :: TypeExpression -- ^ The type expression on the right-hand side.
  }
  deriving (Eq, Typeable, Data)



-- | A @data@ declaration for an algebraic data type.
--
--   Note that the context and the deriving parts of a @data@ declaration are
--   ignored.

data DataDeclaration = Data 
  { dataName     :: Identifier
        -- ^ The name of the type constructor.

  , dataVars     :: [TypeVariable]
        -- ^ The type variables on the left-hand side.

  , dataCons     :: [DataConstructorDeclaration]
        -- ^ The declarations of the data constructors on the right-hand side.

  }
  deriving (Eq, Typeable, Data)



-- | A @newtype@ declaration for a type renaming.
--
--   Note that the context and the deriving parts of a @newtype@ declaration are
--   ignored.

data NewtypeDeclaration = Newtype 
  { newtypeName     :: Identifier       
        -- ^ The name of the type constructor.
  
  , newtypeVars     :: [TypeVariable]   
        -- ^ The type variables of the left-hand side.
  
  , newtypeCon      :: Identifier
        -- ^ The name of the data constructor on the right-hand side.
  
  , newtypeRhs      :: TypeExpression
        -- ^ The type expression on the right-hand side.
  
  }
  deriving (Eq, Typeable, Data)



-- | A @class@ declaration for a type class.
--
--   Note that, except of type signatures of class methods, all other
--   declarations inside the class are ignored.

data ClassDeclaration = Class 
  { superClasses :: [TypeClass]     
        -- ^ The superclasses of this class.
  
  , className    :: Identifier      
        -- ^ The name of this type class.
  
  , classVar     :: TypeVariable    
        -- ^ The type variable constrained by this type class.
  
  , classFuns    :: [Signature]
        -- ^ The type signatures of the class methods.
  
  }
  deriving (Eq, Typeable, Data)



-- | A type signature.

data Signature = Signature
  { signatureName :: Identifier     
        -- ^ The name of the signature, i.e. the name of a variable or function.
  
  , signatureType :: TypeExpression
        -- ^ The type expression of the type signature.
  
  }
  deriving (Eq, Typeable, Data)



-- | An identifier.
--   This data type tags every @String@ occurring in a declaration or a type
--   expression.

newtype Identifier = Ident { unpackIdent :: String }
  deriving (Eq, Ord, Typeable, Data)



-- | A data constructor declaration.

data DataConstructorDeclaration = DataCon 
  { dataConName  :: Identifier
        -- ^ The name of the data constructor.
  
  , dataConTypes :: [BangTypeExpression]
        -- ^ The type arguments of the data constructor.
  
  }
  deriving (Eq, Typeable, Data)



-- | Indicates whether in an algebraic data type declaration a strictness
--   annotation is used.

data BangTypeExpression
  = Banged { withoutBang :: TypeExpression }
      -- ^ A type expression with a strictness flag \"@!@\".

  | Unbanged { withoutBang :: TypeExpression }
      -- ^ A type expression without a strictness flag.

  deriving (Eq, Typeable, Data)



-- | A Haskell type expression. This data type supports also higher-rank
--   functions. Unlike in Haskell98, a type variable must not be applied to
--   type expressions.

data TypeExpression
  = TypeVar TypeVariable
      -- ^ A type variable.

  | TypeCon TypeConstructor [TypeExpression]
      -- ^ A type constructor. This covers algebraic data types, type synonyms,
      --   and type renamings as well as predefined standard data types like
      --   lists and tuples.

  | TypeFun TypeExpression TypeExpression
      -- ^ The function type constructor @->@.

  | TypeFunLab TypeExpression TypeExpression
      -- ^ The function type constructor @->^o@ for the non-bottom-reflecting
      --   logical relation for functions in the languagesubset with seq
      --   for equational theorems.

  | TypeAbs TypeVariable [TypeClass] TypeExpression
      -- ^ The type abstraction constructor @forall@.

  | TypeAbsLab TypeVariable [TypeClass] TypeExpression
      -- ^ The type abstraction constructor @forall^o@, allowing
      --   non-bottom-reflecting logical relations for types the type variable
      --   is instantiated with in the calculus with seq.

  | TypeExp FixedTypeExpression
      -- ^ A variable representing a fixed type expression.

  deriving (Eq, Typeable, Data)



-- | The data type for type constructors.

data TypeConstructor
  = ConUnit        -- ^ The unit type constructor @()@.
  | ConList        -- ^ The list type constructor @[]@.
  | ConTuple Int   -- ^ The tuple type constructors with given arity.
  | ConInt         -- ^ The Haskell type @Int@.
  | ConInteger     -- ^ The Haskell type @Integer@.
  | ConFloat       -- ^ The Haskell type @Float@.
  | ConDouble      -- ^ The Haskell type @Double@.
  | ConChar        -- ^ The Haskell type @Char@.
  | Con Identifier -- ^ Any other type constructor with a given name.
  deriving (Eq, Typeable, Data)



-- | Identifies a Haskell type class.

newtype TypeClass = TC Identifier
  deriving (Eq, Typeable, Data)



-- | Identifies a Haskell type variable

newtype TypeVariable = TV Identifier
  deriving (Eq, Ord, Typeable, Data)



-- | Represents an abbreviation for some fixed type expression.
--   It does not occur in Haskell98 source code, but it can occur in generated
--   theorems.

newtype FixedTypeExpression = TF Identifier
  deriving (Eq, Typeable, Data)




