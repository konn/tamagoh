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
  fromRelations,
  Database,
  universe,
  selectAll,
  HasDatabase,
  Operator (..),
  newDatabase,
  getTrie,
  toOperator,
) where

import Control.Foldl qualified as L
import Control.Functor.Linear qualified as Control
import Control.Lens hiding (universe)
import Control.Monad.Borrow.Pure
import Data.EGraph.EMatch.Relational.Query (Relation (..))
import Data.EGraph.Types
import Data.Foldable qualified as F
import Data.Functor.Classes
import Data.Generics.Labels ()
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue qualified as HMUr
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable)
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
buildDatabase egraph =
  share egraph PL.& \(Ur egraph) -> Control.do
    Ur nodes <- HMUr.toList (egraph .@ hashconsL)
    let go :: [(ENode l, EClassId)] -> [Relation l EClassId] -> BO α (Ur (Database l))
        go [] acc = Control.pure PL.$ Ur PL.$ fromRelations acc
        go ((enode, eid) : rest) acc = Control.do
          Ur (ENode args) <- unsafeCanonicalize enode egraph
          Ur eid' <- unsafeFind egraph eid
          go rest (MkRel {id = eid', args} : acc)
    go nodes []

{- | An operator is a pattern with all metavariables replaced by unit.
NOTE: We must preapare separate tries for each operators with the same
constructor, but non-parametric field! Otherwise, we cannot distinguish, e.g. @Lit 1.0@ vs @Lit 2.0@.
-}
newtype Operator l = Operator {tag :: l Wildcard}

deriving instance (Eq1 l) => Eq (Operator l)

deriving instance (Ord1 l) => Ord (Operator l)

deriving newtype instance (Show1 l) => Show (Operator l)

deriving newtype instance (Hashable1 l) => Hashable (Operator l)

data Database l = Database
  { database :: !(HashMap (Operator l) Trie)
  , universe :: !IntSet
  , selectAll :: ![EClassId]
  }
  deriving (Generic)

deriving instance (Show1 l) => Show (Database l)

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
fromRelations rels =
  let (universe, database) =
        L.fold
          ( (,)
              <$> L.handles folded (L.Fold (\s e -> IS.insert (Trie.toKey e) s) IS.empty id)
              <*> L.premap
                (\rel@MkRel {args} -> (toOperator args, F.toList rel))
                (L.foldByKeyHashMap (Trie.fromRows <$> L.list))
          )
          rels
      selectAll =
        concatMap
          (fmap Trie.fromKey . IS.toList . Trie.rootKeys . snd)
          (sortOn fst $ HM.toList database)
   in Database {..}

newDatabase :: forall l. (HasDatabase l) => Database l
newDatabase = Database mempty mempty mempty

{-# INLINE toOperator #-}
toOperator :: forall l x. (Functor l) => l x -> Operator l
toOperator = Operator . (fmap (const Wildcard))

{-# INLINE getTrie #-}
getTrie :: forall l. (HasDatabase l) => Operator l -> Database l -> Trie
getTrie l Database {database = db} = HM.lookupDefault Trie.empty l db

type instance Index (Database l) = Operator l

type instance IxValue (Database l) = Trie

instance (HasDatabase l) => Ixed (Database l)

instance (HasDatabase l) => At (Database l) where
  at op = #database . at op
  {-# INLINE at #-}

type HasDatabase l = (Hashable1 l, Ord1 l, Functor l, Foldable l)
