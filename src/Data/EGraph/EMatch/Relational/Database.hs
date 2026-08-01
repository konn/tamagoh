{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.EMatch.Relational.Database (
  buildDatabase,
  buildDatabaseForPatterns,
  buildDatabaseForOperators,
  buildDatabaseForPrepared,
  fromRelations,
  Database,
  universe,
  selectAll,
  HasDatabase,
  Operator (..),
  newDatabase,
  getTrie,
  getPreparedTrie,
  toOperator,
  ColumnLayout,
  mkColumnLayout,
  identityColumnLayout,
  permuteColumns,
  PreparedIndexKey,
  mkPreparedIndexKey,
  preparedIndexOperator,
  preparedIndexLayout,
) where

import Control.Foldl qualified as L
import Control.Functor.Linear qualified as Control
import Control.Lens hiding (universe)
import Control.Monad.Borrow.Pure
import Data.DList qualified as DL
import Data.EGraph.EMatch.Relational.Query (Relation (..))
import Data.EGraph.Types
import Data.EGraph.Types.EClasses qualified as EC
import Data.Foldable qualified as F
import Data.Functor.Classes
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.List (sortOn)
import Data.Record.Linear.Borrow.Experimental.PatternMatch
import Data.Trie (Trie)
import Data.Trie qualified as Trie
import GHC.Generics
import Generics.Linear.TH qualified as GL
import Prelude.Linear qualified as PL
import Text.Show.Borrowed (AsCopyableShow (..), Display)

data Wildcard = Wildcard
  deriving (Eq, Ord, Generic)
  deriving anyclass (Hashable)

instance Show Wildcard where
  showsPrec _ _ = showString "_"

GL.deriveGeneric ''Wildcard

deriving via Generically Wildcard instance Copyable Wildcard

deriving via Generically Wildcard instance Clone Wildcard

deriving via Generically Wildcard instance Consumable Wildcard

deriving via Generically Wildcard instance Dupable Wildcard

deriving via Generically Wildcard instance Movable Wildcard

deriving via AsCopyableShow Wildcard instance Display Wildcard

{-# INLINEABLE buildDatabase #-}
buildDatabase ::
  forall l d k α m.
  (HasDatabase l, Traversable l) =>
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Database l))
buildDatabase = buildDatabaseWithIndexes True True False

{- | Build the indexes required by queries produced from e-matching patterns.

Compiled patterns bind every query-head variable in the query body, so they
never use the database-wide 'universe' fallback. The 'Bool' indicates whether
the rule set contains a variable-only pattern and therefore needs 'selectAll'.
-}
{-# INLINEABLE buildDatabaseForPatterns #-}
buildDatabaseForPatterns ::
  forall l d k α m.
  (HasDatabase l, Traversable l) =>
  Bool ->
  Bool ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Database l))
buildDatabaseForPatterns includeSelectAll assumeCanonical =
  buildDatabaseWithIndexes False includeSelectAll assumeCanonical

{- | Build only the per-operator relation tries needed by a prepared LHS rule
set. The 'universe' and 'selectAll' indexes are left empty; callers with a
variable-only query must use 'buildDatabaseForPatterns' instead.
-}
{-# INLINEABLE buildDatabaseForOperators #-}
buildDatabaseForOperators ::
  forall l d k α m.
  (HasDatabase l, Traversable l) =>
  HashSet (Operator l) ->
  Bool ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Database l))
buildDatabaseForOperators operators assumeCanonical =
  buildDatabaseWithOperatorFilter operators assumeCanonical

{- | Build the canonical and reordered operator indexes required by a static
prepared-query set. This is saturation-only: public database builders keep the
prepared map empty, so manually constructed databases retain canonical
matching and planning.
-}
{-# INLINEABLE buildDatabaseForPrepared #-}
buildDatabaseForPrepared ::
  forall l d k α m.
  (HasDatabase l, Traversable l) =>
  HashSet (Operator l) ->
  HashSet (PreparedIndexKey l) ->
  Bool ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Database l))
buildDatabaseForPrepared canonicalOperators preparedIndexes assumeCanonical egraph =
  share egraph PL.& \(Ur egraph) -> Control.do
    Ur classes <- EC.nodeLists (egraph .# #classes)
    let layoutsByOperator =
          HM.map (sortOn id) $
            HM.fromListWith
              (<>)
              [ (operator, [layout])
              | PreparedIndexKey operator layout <- HS.toList preparedIndexes
              ]

        goClasses ::
          [(EClassId, [ENode l])] ->
          [(Operator l, [EClassId])] ->
          [(PreparedIndexKey l, [EClassId])] ->
          BO α (Ur (Database l))
        goClasses [] canonicalRows preparedRows =
          Control.pure PL.$
            Ur PL.$
              Database
                { database = fromRowsByKey canonicalRows
                , preparedDatabase = fromRowsByKey preparedRows
                , universe = IS.empty
                , selectAll = []
                }
        goClasses ((eid, nodes) : rest) canonicalRows preparedRows =
          goNodes eid nodes rest canonicalRows preparedRows

        goNodes ::
          EClassId ->
          [ENode l] ->
          [(EClassId, [ENode l])] ->
          [(Operator l, [EClassId])] ->
          [(PreparedIndexKey l, [EClassId])] ->
          BO α (Ur (Database l))
        goNodes _ [] rest canonicalRows preparedRows =
          goClasses rest canonicalRows preparedRows
        goNodes eid (enode@(ENode args) : nodes) rest canonicalRows preparedRows =
          let !operator = toOperator args
              !needCanonical = HS.member operator canonicalOperators
              !layouts = HM.lookupDefault [] operator layoutsByOperator
           in if not needCanonical && null layouts
                then goNodes eid nodes rest canonicalRows preparedRows
                else
                  let emit canonicalArgs =
                        let !row = F.toList MkRel {id = eid, args = canonicalArgs}
                            !canonicalRows' =
                              if needCanonical
                                then (operator, row) : canonicalRows
                                else canonicalRows
                            !preparedRows' =
                              F.foldl'
                                ( \acc layout ->
                                    (PreparedIndexKey operator layout, permuteColumnsUnsafe layout row) : acc
                                )
                                preparedRows
                                layouts
                         in goNodes eid nodes rest canonicalRows' preparedRows'
                   in if assumeCanonical
                        then emit args
                        else Control.do
                          Ur (ENode canonicalArgs) <- unsafeCanonicalize enode egraph
                          emit canonicalArgs
    goClasses classes [] []

{-# INLINEABLE buildDatabaseWithIndexes #-}
buildDatabaseWithIndexes ::
  forall l d k α m.
  (HasDatabase l, Traversable l) =>
  Bool ->
  Bool ->
  {- | May class node sets be trusted as canonical (the graph's
  @nodeSetsCanonical@ flag, set by rebuild's canonical trim)? Only the
  saturation loop passes 'True', and only for builds that follow a
  rebuild; every public entry point re-canonicalizes each row.
  -}
  Bool ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Database l))
buildDatabaseWithIndexes includeUniverse includeSelectAll assumeCanonical egraph =
  buildDatabaseWithFilter includeUniverse includeSelectAll assumeCanonical Nothing egraph

{-# INLINEABLE buildDatabaseWithOperatorFilter #-}
buildDatabaseWithOperatorFilter ::
  forall l d k α m.
  (HasDatabase l, Traversable l) =>
  HashSet (Operator l) ->
  Bool ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Database l))
buildDatabaseWithOperatorFilter operators assumeCanonical =
  buildDatabaseWithFilter False False assumeCanonical (Just operators)

{-# INLINEABLE buildDatabaseWithFilter #-}
buildDatabaseWithFilter ::
  forall l d k α m.
  (HasDatabase l, Traversable l) =>
  Bool ->
  Bool ->
  Bool ->
  Maybe (HashSet (Operator l)) ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Database l))
buildDatabaseWithFilter includeUniverse includeSelectAll assumeCanonical operatorFilter egraph =
  share egraph PL.& \(Ur egraph) -> Control.do
    Ur classes <- EC.nodeLists (egraph .# #classes)
    let goClasses :: [(EClassId, [ENode l])] -> [Relation l EClassId] -> BO α (Ur (Database l))
        goClasses [] acc =
          Control.pure PL.$ Ur PL.$ fromRelationsWithIndexes includeUniverse includeSelectAll acc
        goClasses ((eid, nodes) : rest) acc = goNodes eid nodes rest acc

        goNodes :: EClassId -> [ENode l] -> [(EClassId, [ENode l])] -> [Relation l EClassId] -> BO α (Ur (Database l))
        goNodes _ [] rest acc = goClasses rest acc
        goNodes eid (enode@(ENode args) : nodes) rest acc
          | Just operators <- operatorFilter
          , not (HS.member (toOperator args) operators) =
              goNodes eid nodes rest acc
          | assumeCanonical =
              goNodes eid nodes rest (MkRel {id = eid, args} : acc)
          | otherwise = Control.do
              Ur (ENode canonicalArgs) <- unsafeCanonicalize enode egraph
              goNodes eid nodes rest (MkRel {id = eid, args = canonicalArgs} : acc)
    goClasses classes []

{- | An operator is a pattern with all metavariables replaced by unit.
NOTE: We must preapare separate tries for each operators with the same
constructor, but non-parametric field! Otherwise, we cannot distinguish, e.g. @Lit 1.0@ vs @Lit 2.0@.
-}
newtype Operator l = Operator {tag :: l Wildcard}

deriving instance (Eq1 l) => Eq (Operator l)

deriving instance (Ord1 l) => Ord (Operator l)

deriving newtype instance (Show1 l) => Show (Operator l)

deriving newtype instance (Hashable1 l) => Hashable (Operator l)

newtype ColumnLayout = ColumnLayout [Int]
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

-- | Validate a total permutation of @[0 .. width - 1]@.
mkColumnLayout :: Int -> [Int] -> Maybe ColumnLayout
mkColumnLayout width layout
  | length layout == width
  , IS.fromList layout == IS.fromDistinctAscList [0 .. width - 1] =
      Just (ColumnLayout layout)
  | otherwise = Nothing

identityColumnLayout :: Int -> ColumnLayout
identityColumnLayout width = ColumnLayout [0 .. width - 1]

-- | Reorder a row when its width agrees with the validated layout.
permuteColumns :: ColumnLayout -> [a] -> Maybe [a]
permuteColumns layout@(ColumnLayout columns) row
  | length row == length columns = Just (permuteColumnsUnsafe layout row)
  | otherwise = Nothing

permuteColumnsUnsafe :: ColumnLayout -> [a] -> [a]
permuteColumnsUnsafe (ColumnLayout layout) row = map (row !!) layout

data PreparedIndexKey l = PreparedIndexKey !(Operator l) !ColumnLayout
  deriving stock (Generic)

deriving instance (Eq1 l) => Eq (PreparedIndexKey l)

deriving instance (Ord1 l) => Ord (PreparedIndexKey l)

deriving instance (Show1 l) => Show (PreparedIndexKey l)

instance (Hashable1 l) => Hashable (PreparedIndexKey l) where
  hashWithSalt salt (PreparedIndexKey operator layout) =
    hashWithSalt (hashWithSalt salt operator) layout

-- | Pair an operator with a layout only when their relation widths agree.
mkPreparedIndexKey ::
  (Foldable l) =>
  Operator l ->
  ColumnLayout ->
  Maybe (PreparedIndexKey l)
mkPreparedIndexKey operator@(Operator tag) layout@(ColumnLayout columns)
  | length columns == 1 + F.length tag = Just (PreparedIndexKey operator layout)
  | otherwise = Nothing

preparedIndexOperator :: PreparedIndexKey l -> Operator l
preparedIndexOperator (PreparedIndexKey operator _) = operator

preparedIndexLayout :: PreparedIndexKey l -> ColumnLayout
preparedIndexLayout (PreparedIndexKey _ layout) = layout

data Database l = Database
  { database :: !(HashMap (Operator l) Trie)
  , preparedDatabase :: !(HashMap (PreparedIndexKey l) Trie)
  , universe :: !IntSet
  , selectAll :: ![EClassId]
  }
  deriving (Generic)

instance (Show1 l) => Show (Database l) where
  showsPrec d Database {database, universe, selectAll} =
    showParen (d > 10) $
      showString "Database {database = "
        . shows database
        . showString ", universe = "
        . shows universe
        . showString ", selectAll = "
        . shows selectAll
        . showString "}"

{-# INLINE universe #-}
universe :: Database l -> IntSet
universe = (.universe)

{- | Every relation root, retaining cross-relation multiplicity as hegg's
@SelectAllQuery@ does.
-}
{-# INLINE selectAll #-}
selectAll :: Database l -> [EClassId]
selectAll = (.selectAll)

{-# INLINEABLE fromRelations #-}
fromRelations :: (HasDatabase l) => [Relation l EClassId] -> Database l
fromRelations = fromRelationsWithIndexes True True

{-# INLINEABLE fromRelationsWithIndexes #-}
fromRelationsWithIndexes ::
  (HasDatabase l) => Bool -> Bool -> [Relation l EClassId] -> Database l
fromRelationsWithIndexes includeUniverse includeSelectAll rels =
  let databaseFold =
        L.premap
          (\rel@MkRel {args} -> (toOperator args, F.toList rel))
          (L.foldByKeyHashMap (Trie.fromRows <$> L.list))
      (universe, database) =
        if includeUniverse
          then
            L.fold
              ( (,)
                  <$> L.handles folded (L.Fold (\s e -> IS.insert (Trie.toKey e) s) IS.empty id)
                  <*> databaseFold
              )
              rels
          else (IS.empty, L.fold databaseFold rels)
      selectAll =
        if includeSelectAll
          then
            concatMap
              (fmap Trie.fromKey . IS.toList . Trie.rootKeys . snd)
              (sortOn fst $ HM.toList database)
          else []
   in Database {preparedDatabase = HM.empty, ..}

newDatabase :: forall l. (HasDatabase l) => Database l
newDatabase = Database mempty mempty mempty mempty

{-# INLINE toOperator #-}
toOperator :: forall l x. (Functor l) => l x -> Operator l
toOperator = Operator . (fmap (const Wildcard))

{-# INLINE getTrie #-}
getTrie :: forall l. (HasDatabase l) => Operator l -> Database l -> Trie
getTrie l Database {database = db} = HM.lookupDefault Trie.empty l db

{-# INLINEABLE getPreparedTrie #-}
getPreparedTrie ::
  forall l.
  (HasDatabase l) =>
  PreparedIndexKey l ->
  Database l ->
  Maybe Trie
getPreparedTrie key Database {preparedDatabase} = HM.lookup key preparedDatabase

type instance Index (Database l) = Operator l

type instance IxValue (Database l) = Trie

instance (HasDatabase l) => Ixed (Database l)

instance (HasDatabase l) => At (Database l) where
  at op = #database . at op
  {-# INLINE at #-}

type HasDatabase l = (Hashable1 l, Ord1 l, Functor l, Foldable l)

{-# INLINEABLE fromRowsByKey #-}
fromRowsByKey :: (Hashable key) => [(key, [EClassId])] -> HashMap key Trie
fromRowsByKey =
  HM.map (Trie.fromRows . DL.toList)
    . HM.fromListWith (flip (<>))
    . map (fmap DL.singleton)
