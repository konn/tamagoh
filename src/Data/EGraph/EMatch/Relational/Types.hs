{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.EMatch.Relational.Types (
  Relation (..),
  fromRelations,
  Atom (..),
  varQ,
  idQ,
  Query (..),
  Database,
  HasDatabase (..),
  newDatabase,
  getDatabase,
  insertDb,
) where

import Data.Coerce (coerce)
import Data.EGraph.Types
import Data.Foldable qualified as F
import Data.Functor.Classes
import Data.Hashable
import Data.Hashable.Lifted
import Data.List.NonEmpty (NonEmpty)
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

newtype Atom l v = LangQuery (Pattern (Relation l) (Either EClassId v))
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 (Atom l)

deriveShow1 ''Atom

data Query l v
  = SelectAll v
  | [v] :- NonEmpty (Atom l v)
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 (Query l)

deriveShow1 ''Query

varQ :: v -> Atom l v
varQ v = LangQuery $ Metavar (Right v)

idQ :: EClassId -> Atom l v
idQ eid = LangQuery $ Metavar (Left eid)

newtype Database l = Database (Database_ l)

fromRelations :: (HasDatabase l) => [Relation l EClassId] -> Database l
fromRelations = foldr (\MkRel {id, args} -> insertDb id $ ENode args) newDatabase

newDatabase :: forall l. (HasDatabase l) => Database l
newDatabase = Database $ newDatabase_ @l

getDatabase :: forall l. (HasDatabase l) => l () -> Database l -> Trie
getDatabase = coerce $ getDatabase_ @l

insertDb :: forall l. (HasDatabase l) => EClassId -> ENode l -> Database l -> Database l
insertDb = coerce $ insertDb_ @l

class HasDatabase l where
  type Database_ l
  newDatabase_ :: Database_ l
  getDatabase_ :: l () -> Database_ l -> Trie
  insertDb_ :: EClassId -> ENode l -> Database_ l -> Database_ l

type GenericHasDatabase l = (Generic1 l, HasDatabase (Rep1 l))

instance (GenericHasDatabase l) => HasDatabase (Generically1 l) where
  type Database_ (Generically1 l) = Database_ (Rep1 l)
  newDatabase_ = newDatabase_ @(Rep1 l)
  {-# INLINE newDatabase_ #-}
  getDatabase_ = coerce $ getDatabase_ @(Rep1 l) . from1 @_ @l
  {-# INLINE getDatabase_ #-}
  insertDb_ eid (ENode (Generically1 l)) = coerce $ insertDb_ @(Rep1 l) eid (ENode (from1 l))
  {-# INLINE insertDb_ #-}

instance HasDatabase U1 where
  type Database_ U1 = Trie
  newDatabase_ = Trie.empty
  getDatabase_ = const id
  insertDb_ eid (ENode U1) = Trie.insert [eid]

instance HasDatabase V1 where
  type Database_ V1 = ()
  newDatabase_ = ()
  {-# INLINE newDatabase_ #-}
  getDatabase_ = \case {}
  {-# INLINE getDatabase_ #-}
  insertDb_ = \_ -> \case {}
  {-# INLINE insertDb_ #-}

instance (HasDatabase f, HasDatabase g) => HasDatabase (f :+: g) where
  type Database_ (f :+: g) = Database_ f :!: Database_ g
  newDatabase_ = newDatabase_ @f :!: newDatabase_ @g
  {-# INLINE newDatabase_ #-}
  getDatabase_ = \case
    L1 x -> getDatabase_ x . \(dbf :!: _) -> dbf
    R1 y -> getDatabase_ y . \(_ :!: dbg) -> dbg
  {-# INLINE getDatabase_ #-}
  insertDb_ eid (ENode (L1 node)) (dbf :!: dbg) =
    insertDb_ eid (ENode node) dbf :!: dbg
  insertDb_ eid (ENode (R1 node)) (dbf :!: dbg) =
    dbf :!: insertDb_ eid (ENode node) dbg
  {-# INLINE insertDb_ #-}

instance (HasDatabase f) => HasDatabase (D1 i f) where
  type Database_ (D1 i f) = Database_ f
  newDatabase_ = newDatabase_ @f
  {-# INLINE newDatabase_ #-}
  getDatabase_ = coerce $ getDatabase_ @f
  {-# INLINE getDatabase_ #-}
  insertDb_ = coerce $ insertDb_ @f
  {-# INLINE insertDb_ #-}

instance (Foldable f) => HasDatabase (C1 i f) where
  type Database_ (C1 i f) = Trie
  newDatabase_ = Trie.empty
  {-# INLINE newDatabase_ #-}
  getDatabase_ = \_ -> coerce
  {-# INLINE getDatabase_ #-}
  insertDb_ eid (ENode (M1 node)) db =
    Trie.insert (F.toList MkRel {id = eid, args = node}) db
  {-# INLINE insertDb_ #-}