


-- | Defines global checks, i.e. checks which need to look at more than one
--   declaration at a time.

module Language.Haskell.FreeTheorems.Frontend.CheckGlobal (checkGlobal) where



import Control.Monad (when)
import Control.Monad.Error (throwError)
import Control.Monad.Writer (tell)
import Data.Generics (Typeable, Data, everything, everywhereM, extQ, mkQ, mkM)
import Data.List (intersperse, partition, nub, intersect)
import qualified Data.Map as Map (Map, empty, insert, lookup)
import Data.Maybe (mapMaybe, fromJust)
import qualified Data.Set as Set
    ( Set, empty, singleton, union, fromList, isSubsetOf, member, difference
    , partition, null, elems, size )

import Language.Haskell.FreeTheorems.BasicSyntax
import Language.Haskell.FreeTheorems.ValidSyntax
import Language.Haskell.FreeTheorems.Frontend.Error





------- Global checks ---------------------------------------------------------


-- | Perform global checks, i.e. looks at more than one declaration at a time.
--   The following restrictions will be checked:
--
--   * Every symbol is declared at most once.
--   
--   * Every type constructor is used in the arity it was declared with.
--
--   * Type synonyms are not mutually recursive.
--
--   * The type class hierachy is acyclic.
--
--   * In every type expression, only declared type constructors and only
--     declared type classes occur.

checkGlobal :: [ValidDeclaration] -> [Declaration] -> Checked [Declaration] 
checkGlobal vds ds =
  -- run through all declarations in 'ds' to test whether any name occurs twice
  checkUnique vds ds

  -- then, run through all remaining declarations and check the arities of all
  -- type constructors
  >>= checkArities vds

  -- extract all type synonyms which are not mutually recursive
  >>= checkAcyclicTypeSynonyms

  -- extract all type classes whose type hierarchy is acyclic
  >>= checkAcyclicTypeClasses

  -- finally, take only those declarations which contain only declared type
  -- constructors and type classes
  >>= checkAllConsAndClassesDeclared vds





------- Check that declarations are unique ------------------------------------


-- | Checks that every name has at most one declaration, or that there are no
--   two declarations with the same name.
--
--   The first argument gives a list of already checked declarations against
--   which the second argument is tested. The resulting list contains all
--   elements of the first argument and only the valid declarations of the
--   second argument.

checkUnique :: [ValidDeclaration] -> [Declaration] -> Checked [Declaration]
checkUnique vds ds =
  let -- extract all known declaration names, both from 'vds' and from 'ds'
      knownNames = map getDeclarationName (map rawDeclaration vds ++ ds)
    
      -- test if the name of a declaration occurs more than once in 'knownNames'
      occursMoreThanOnce d = 
        let allOccurrences = filter (== (getDeclarationName d)) knownNames
         in length allOccurrences > 1
 
      -- construct a list 'us' of all unique declarations and a list 'ms' of all
      -- declarations which names occur more than once
      (ms, us) = partition occursMoreThanOnce ds

      -- extract the names which occur more than once
      multiples = map unpackIdent . nub . map getDeclarationName $ ms

      error s = [pp ("Multiple declarations for `" ++ s ++ "'.")]
   
   in do when (not (null multiples)) $ mapM_ (tell . error) multiples
         return us





------- Check arities of type constructors ------------------------------------


-- | Checks the arity of all type constructors. If an undeclared type
--   constructor is found, no arity check will be performed, because
--   any declaration containing undeclared type constructors will be filtered
--   out in the next step of checking (see 'checkGlobal').

checkArities :: [ValidDeclaration] -> [Declaration] -> Checked [Declaration]
checkArities vds ds =
  let -- build a map of arities
      mkMap d m = case getDeclarationArity d of
                    Nothing     -> m
                    Just arity  -> Map.insert (getDeclarationName d) arity m
      arityMap = foldr mkMap Map.empty (map rawDeclaration vds ++ ds)

   in foldChecks (\d -> inDecl d $ checkArity arityMap d) ds



-- | Checks the arities of all occurring type constructors according to the 
--   given arity map.

checkArity :: (Typeable a, Data a) => Map.Map Identifier Int -> a -> ErrorOr a
checkArity arityMap = everywhereM (mkM checkCorrectArity)
  where
    -- extracts the type constructors and relates expected and found arities
    checkCorrectArity t = case t of
      TypeCon ConUnit ts    -> errorArity t "()"      0 (length ts)
      TypeCon ConList ts    -> errorArity t "[]"      1 (length ts)
      TypeCon ConInt ts     -> errorArity t "Int"     0 (length ts)
      TypeCon ConInteger ts -> errorArity t "Integer" 0 (length ts)
      TypeCon ConFloat ts   -> errorArity t "Float"   0 (length ts)
      TypeCon ConDouble ts  -> errorArity t "Double"  0 (length ts)
      TypeCon ConChar ts    -> errorArity t "Char"    0 (length ts)
      TypeCon (Con c) ts    -> case Map.lookup c arityMap of
                                 Nothing -> return t
                                 Just i  -> let n = unpackIdent c
                                             in errorArity t n i (length ts)
      
      TypeCon (ConTuple n) ts -> do
        errorArity t ("(" ++ replicate (n-1) ',' ++ ")") n (length ts)
        errorIf (n < 2) $
          pp "A tuple type constructor must have at least two arguments."
        return t
                                 
      otherwise             -> return t

    -- performs the actual checking and error message creation
    errorArity t conName expected found = 
      let args k = case k of
            0         -> "no argument"
            1         -> "1 argument"
            otherwise -> show k ++ " arguments"
       in do errorIf (found /= expected) $
                pp ("Type constructor `" ++ conName ++ "' was declared to have "
                    ++ args expected ++ ", but it is used with " ++ args found 
                    ++ ".")
             return t
   




------- Acyclic tests ---------------------------------------------------------


-- | Checks that type synonym declarations are not mutually recursive.
--   Error messages are created for all type synonym declarations which are
--   mutually recursive with other type synonym declarations.

checkAcyclicTypeSynonyms :: [Declaration] -> Checked [Declaration]
checkAcyclicTypeSynonyms ds =
  let -- gets the name of a type synonym declaration or Nothing
      getTypeSynonymName d = 
        case d of { TypeDecl d -> Just (typeName d) ; otherwise -> Nothing }
      
      -- the list of all known type synonym names
      allTypeSynonymNames = mapMaybe getTypeSynonymName ds

      -- extracts a type synonym name from a type expression
      occurringTypeSynonyms t = case t of
        TypeCon (Con c) _ -> if c `elem` allTypeSynonymNames 
                               then Set.singleton c
                               else Set.empty
        otherwise         -> Set.empty
      
      -- given an element (e.g. a declaration), this function determines all
      -- type synonyms which this element is based on
      getDependencies = 
        everything Set.union (Set.empty `mkQ` occurringTypeSynonyms)

      -- the error message for all unaccepted declarations
      error = "Declarations of type synonyms must not be mutually recursive."

      -- filter all mutually recursive declarations
   in checkDependencyGraph ds getDependencies error "type synonym"



-- | Checks that the type class hierarchy is acyclic. An error message is
--   created for every type class which is part of a cycle.
--
--   Undeclared type classes occurring as superclasses are ignored. They will
--   be filtered out in the next step (see 'checkGlobal').

checkAcyclicTypeClasses :: [Declaration] -> Checked [Declaration]
checkAcyclicTypeClasses ds =
  let -- gets the name of a class declaration or Nothing
      getClassName d = 
        case d of { ClassDecl d -> Just (className d) ; otherwise -> Nothing }
      
      -- the list of all known class names
      allClassNames = mapMaybe getClassName ds

      -- given a class declaration, this function returns the set of all
      -- superclasses having a known declaration
      getSuperClasses d = case d of
        ClassDecl d -> let cs = map (\(TC c) -> c) . superClasses $ d
                        in Set.fromList (cs `intersect` allClassNames)
        otherwise   -> Set.empty

      -- the error message for all unaccepted declarations
      error =
        "The type class hierarchy formed by the type classes and their "
        ++ "superclasses must not be acyclic."

      -- filter all acyclic type classes
   in checkDependencyGraph ds getSuperClasses error "type class"



-- | Applies 'recursivePartition' to the arguments and generates error messages
--   for all erroneous declarations.

checkDependencyGraph :: 
    [Declaration] 
    -> (Declaration -> Set.Set Identifier) 
    -> String
    -> String
    -> Checked [Declaration]

checkDependencyGraph ds getDependencies errMsg tag = do
  let (ok, err) = recursivePartition ds getDependencies
  when (not (null err)) $
    tell [pp (errMsg
              ++ violating tag 
                   (map (unpackIdent . getDeclarationName . fst) err))]
  return ok



-- | Partitions a list of declarations using a dependency function.
--   Every declaration, which depends only on the declarations given by the
--   third argument, is put into the left set.
--   Every declaration, which depends only on the declarations already in the
--   left set, is put also into the left set. This step is recursively repeated
--   until no more declarations are added to the left set.
--   This function terminates if the first argument is a finite list.

recursivePartition :: 
    [Declaration] 
    -> (Declaration -> Set.Set Identifier) 
    -> ([Declaration], [(Declaration, Set.Set Identifier)])

recursivePartition decls getDependencies =
  let -- to increase efficency, calculate the dependencies beforehand
      -- and use the declaration names as keys (declaration names are unique)
      mkMap d m = Map.insert (getDeclarationName d) (getDependencies d) m
      depMap = foldr mkMap Map.empty decls

      -- checks if 'd' depends only on 'ds' and 'extras', 
      -- i.e. if 'd' is fully contained in 'ds' and 'extras'
      dependsOn d ds = 
        let deps = fromJust (Map.lookup d depMap)
         in deps `Set.isSubsetOf` ds

      -- implements the actual partitioning
      select (ds, rs) = 
        let (ds', rs') = Set.partition (\d -> d `dependsOn` ds) rs
         in if Set.null ds'
              then (ds, rs)
              else select (ds `Set.union` ds', rs')

      -- run the partitioning, 'ok' is the accepted set while 'err' contains
      -- all erroneous declarations
      (s1, s2) = select (Set.empty, Set.fromList (map getDeclarationName decls))
      (ok, err) = partition (\d -> getDeclarationName d `Set.member` s1) decls

      -- reduce the mapping to erroneous declarations only such that every
      -- declaration is only mapped to names of erroneous declarations
      getErrDeps d = 
        let deps = fromJust (Map.lookup (getDeclarationName d) depMap)
         in deps `Set.difference` s1
      errMap = foldr (\d m -> (d, getErrDeps d) : m) [] err

   in (ok, errMap)





------- Check declared type constuctors and classes ---------------------------


data Name
  = CON Identifier
  | CLA Identifier
  | OTH Identifier
  deriving (Eq, Ord)


getDeclarationName' :: Declaration -> Name
getDeclarationName' (TypeDecl d)    = CON (typeName d)
getDeclarationName' (DataDecl d)    = CON (dataName d)
getDeclarationName' (NewtypeDecl d) = CON (newtypeName d)
getDeclarationName' (ClassDecl d)   = CLA (className d)
getDeclarationName' (TypeSig s)     = OTH (signatureName s)


unpackName :: Name -> Identifier
unpackName (CON c) = c
unpackName (CLA c) = c
unpackName (OTH c) = c



-- | Checks that all declarations depend only on declared type constructors and
--   declared type classes.

checkAllConsAndClassesDeclared :: 
    [ValidDeclaration] -> [Declaration] -> Checked [Declaration]
checkAllConsAndClassesDeclared vds ds = 
  let -- gets a type constructor name occurring in a type expression
      getCons t = case t of
        TypeCon (Con c) _ -> Set.singleton (CON c)
        otherwise         -> Set.empty

      -- gets a type class name
      getClasses (TC c) = Set.singleton (CLA c)

      -- gets all type class names and all type constructor names occurring
      -- in an element (e.g. a declaration)
      getDependencies = 
        everything Set.union (const Set.empty `extQ` getCons `extQ` getClasses)

      -- the error message for all unaccepted declarations
      error d is = 
        inDecl d $
          throwError $
            pp ("The following type constructors or type classes are not "
                ++ "declared or their declaration contains errors: "
                ++ (concat . intersperse ", " . map (unpackIdent . unpackName) 
                   $ is))

      (ok, err) = partitionDeclared ds getDependencies (map rawDeclaration vds)

      -- filter all declarations which only depend on declared type constructors
      -- and declared type classes
   in do tell (mapMaybe (\(d, is) -> getError . error d . Set.elems $ is) err)
         return ok
  


-- | Partitions a given list to all those declarations which don't rely 
--   directly or indirectly on undeclared type constructors or type classes.
--   Compare with 'recursivePartition'.

partitionDeclared :: 
    [Declaration] 
    -> (Declaration -> Set.Set Name) 
    -> [Declaration]
    -> ([Declaration], [(Declaration, Set.Set Name)])

partitionDeclared decls getDependencies extraDecls =
  let -- to increase efficency, calculate the dependencies beforehand
      -- and use the declaration names as keys (declaration names are unique)
      mkMap d m = Map.insert (getDeclarationName' d) (getDependencies d) m
      depMap = foldr mkMap Map.empty decls

      -- the list of extra names
      extras = Set.fromList (map getDeclarationName' extraDecls)

      -- checks if 'd' depends only on 'ds' and 'extras', 
      -- i.e. if 'd' is fully contained in 'ds' and 'extras'
      dependsOn d ds = 
        let deps = fromJust (Map.lookup d depMap)
         in deps `Set.isSubsetOf` (extras `Set.union` ds)

      -- implements the actual partitioning
      select (ds, es) = 
        let (ds', es') = Set.partition (\d -> d `dependsOn` ds) ds
         in if Set.size ds == Set.size ds'
              then (ds, es)
              else select (ds', es `Set.union` es')

      -- run the partitioning, 'ok' is the accepted set while 'err' contains
      -- all erroneous declarations
      (s1, s2) = select (Set.fromList (map getDeclarationName' decls), Set.empty)
      (ok, err) = partition (\d -> getDeclarationName' d `Set.member` s1) decls

      -- reduce the mapping to erroneous declarations only such that every
      -- declaration is only mapped to names of erroneous declarations
      getErrDeps d = 
        let deps = fromJust (Map.lookup (getDeclarationName' d) depMap)
         in deps `Set.difference` (extras `Set.union` s1)
      errMap = foldr (\d m -> (d, getErrDeps d) : m) [] err

   in (ok, errMap)



