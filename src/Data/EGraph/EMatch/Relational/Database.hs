{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
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
  HasDatabase (..),
  newDatabase,
  getTrie,
  insertDb,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Coerce (coerce)
import Data.EGraph.EMatch.Relational.Query (Relation (..))
import Data.EGraph.Types
import Data.Foldable qualified as F
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear ((.#))
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Maybe (fromJust)
import Data.Strict (Pair (..), (:!:))
import Data.Trie (Trie)
import Data.Trie qualified as Trie
import Data.Unrestricted.Linear
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Lifted
import GHC.Generics
import Prelude.Linear qualified as PL

buildDatabase ::
  (HasDatabase l, Movable1 l, Traversable l) =>
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Database l))
buildDatabase egraph =
  share egraph PL.& \(Ur egraph) -> Control.do
    Ur nodes <- HMB.toList (egraph .# hashconsL)
    Ur nodes <- Control.fmap move PL.$
      Data.forM nodes \(enode, id) ->
        move (enode, id) PL.& \(Ur (enode, id)) ->
          (,)
            Control.<$> (unur PL.. Ur.lift fromJust Control.<$> canonicalize enode egraph)
            Control.<*> (unur Control.<$> unsafeFind egraph id)
    Control.pure PL.$
      Ur $
        fromRelations $
          PL.map (\(ENode args, id) -> MkRel {id, args}) nodes

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
