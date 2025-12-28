{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.EMatch.Relational.Types (
  Relation (..),
  fromRelations,
  Atom (..),
  findVars,
  Query (..),
  ConjunctiveQuery (..),
  Database,
  universe,
  HasDatabase (..),
  newDatabase,
  getTrie,
  insertDb,
) where

import Data.Coerce (coerce)
import Data.EGraph.Types
import Data.Foldable qualified as F
import Data.Functor.Classes
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable
import Data.Hashable.Lifted
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (mapMaybe)
import Data.Strict (Pair (..), (:!:))
import Data.Trie (Trie)
import Data.Trie qualified as Trie
import GHC.Generics
import Text.Show.Deriving

data Relation l v = MkRel {id :: !v, args :: !(l v)}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

deriveShow1 ''Relation

deriving via Generically1 (Relation l) instance (Eq1 l) => Eq1 (Relation l)

deriving via Generically1 (Relation l) instance (Ord1 l) => Ord1 (Relation l)

deriving anyclass instance (Hashable1 l) => Hashable1 (Relation l)

data EClassIdOrVar v
  = EClassId !EClassId
  | Var !v
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 EClassIdOrVar

deriveShow1 ''EClassIdOrVar

newtype Atom l v = Atom (Relation l (EClassIdOrVar v))
  deriving (Generic, Generic1, Functor, Foldable, Traversable)
  deriving (Eq1, Ord1) via Generically1 (Atom l)

deriving stock instance (Show1 l, Show v) => Show (Atom l v)

deriving stock instance (Eq1 l, Eq v) => Eq (Atom l v)

deriving stock instance (Ord1 l, Ord v) => Ord (Atom l v)

deriving anyclass instance (Hashable1 l, Hashable v) => Hashable (Atom l v)

deriving anyclass instance (Hashable1 l, Functor l) => Hashable1 (Atom l)

deriveShow1 ''Atom

data Query l v
  = SelectAll v
  | Conj (ConjunctiveQuery l v)
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 (Query l)

data ConjunctiveQuery l v
  = (:-) {head :: [v], body :: NonEmpty (Atom l v)}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 (ConjunctiveQuery l)

deriveShow1 ''ConjunctiveQuery
deriveShow1 ''Query

findVars :: (Eq v, Foldable l) => v -> Atom l v -> Maybe (NonEmpty Int)
findVars v (Atom pattern) =
  NE.nonEmpty
    $ mapMaybe
      ( uncurry \cases
          !i (Var v') | v == v' -> Just i
          _ _ -> Nothing
      )
    $ zip [0 ..]
    $ F.toList pattern

data Database l = Database
  { database :: !(Database_ l)
  , universe :: !(HashSet EClassId)
  }
  deriving (Generic)

universe :: Database l -> HashSet EClassId
universe = (.universe)

fromRelations :: (HasDatabase l, Foldable l) => [Relation l EClassId] -> Database l
fromRelations = foldr (\MkRel {id, args} -> insertDb id $ ENode args) newDatabase

newDatabase :: forall l. (HasDatabase l) => Database l
newDatabase = Database (newDatabase_ @l) mempty

getTrie :: forall l x. (HasDatabase l) => l x -> Database l -> Trie
getTrie l (Database db _) = getTrie_ @l l db

insertDb :: forall l. (Foldable l, HasDatabase l) => EClassId -> ENode l -> Database l -> Database l
insertDb eid enode (Database db universe) =
  Database
    (insertDb_ @l eid enode db)
    (foldl' (flip HS.insert) (HS.insert eid universe) enode.unwrap)

class HasDatabase l where
  type Database_ l
  newDatabase_ :: Database_ l
  getTrie_ :: l x -> Database_ l -> Trie
  insertDb_ :: EClassId -> ENode l -> Database_ l -> Database_ l

type GenericHasDatabase l = (Foldable l, Generic1 l, HasDatabase (Rep1 l))

instance
  (GenericHasDatabase l) =>
  HasDatabase (Generically1 l)
  where
  type Database_ (Generically1 l) = Database_ (Rep1 l)
  newDatabase_ = newDatabase_ @(Rep1 l)
  {-# INLINE newDatabase_ #-}
  getTrie_ :: forall x. Generically1 l x -> Database_ (Generically1 l) -> Trie
  getTrie_ = coerce $ getTrie_ @(Rep1 l) @x . from1 @_ @l
  {-# INLINE getTrie_ #-}
  insertDb_ eid (ENode (Generically1 l)) = coerce $ insertDb_ @(Rep1 l) eid (ENode (from1 l))
  {-# INLINE insertDb_ #-}

instance HasDatabase U1 where
  type Database_ U1 = Trie
  newDatabase_ = Trie.empty
  getTrie_ = const id
  insertDb_ eid (ENode U1) = Trie.insert [eid]

instance HasDatabase V1 where
  type Database_ V1 = ()
  newDatabase_ = ()
  {-# INLINE newDatabase_ #-}
  getTrie_ = \case {}
  {-# INLINE getTrie_ #-}
  insertDb_ = \_ -> \case {}
  {-# INLINE insertDb_ #-}

instance (HasDatabase f, HasDatabase g) => HasDatabase (f :+: g) where
  type Database_ (f :+: g) = Database_ f :!: Database_ g
  newDatabase_ = newDatabase_ @f :!: newDatabase_ @g
  {-# INLINE newDatabase_ #-}
  getTrie_ = \case
    L1 x -> getTrie_ x . \(dbf :!: _) -> dbf
    R1 y -> getTrie_ y . \(_ :!: dbg) -> dbg
  {-# INLINE getTrie_ #-}
  insertDb_ eid (ENode (L1 node)) (dbf :!: dbg) =
    insertDb_ eid (ENode node) dbf :!: dbg
  insertDb_ eid (ENode (R1 node)) (dbf :!: dbg) =
    dbf :!: insertDb_ eid (ENode node) dbg
  {-# INLINE insertDb_ #-}

instance (HasDatabase f) => HasDatabase (D1 i f) where
  type Database_ (D1 i f) = Database_ f
  newDatabase_ = newDatabase_ @f
  {-# INLINE newDatabase_ #-}
  getTrie_ :: forall x. D1 i f x -> Database_ (D1 i f) -> Trie
  getTrie_ = coerce $ getTrie_ @f @x
  {-# INLINE getTrie_ #-}
  insertDb_ = coerce $ insertDb_ @f
  {-# INLINE insertDb_ #-}

instance (Foldable f) => HasDatabase (C1 i f) where
  type Database_ (C1 i f) = Trie
  newDatabase_ = Trie.empty
  {-# INLINE newDatabase_ #-}
  getTrie_ :: C1 i f x -> Database_ (C1 i f) -> Trie
  getTrie_ = flip const
  {-# INLINE getTrie_ #-}
  insertDb_ eid (ENode (M1 node)) db =
    Trie.insert (F.toList MkRel {id = eid, args = node}) db
  {-# INLINE insertDb_ #-}