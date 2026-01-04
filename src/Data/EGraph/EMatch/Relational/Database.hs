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
  HasDatabase,
  Operator (..),
  newDatabase,
  getTrie,
  insertDb,
  toOperator,
) where

import Control.Arrow ((>>>))
import Control.Functor.Linear qualified as Control
import Control.Lens hiding (universe)
import Control.Monad.Borrow.Pure
import Data.EGraph.EMatch.Relational.Query (Relation (..))
import Data.EGraph.Types
import Data.Foldable qualified as F
import Data.Functor.Classes
import Data.Functor.Linear qualified as Data
import Data.Generics.Labels ()
import Data.HasField.Linear ((.#))
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import Data.Maybe (fromMaybe)
import Data.Trie (Trie)
import Data.Trie qualified as Trie
import Data.Unrestricted.Linear
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Lifted
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

deriving via Generically Wildcard instance Consumable Wildcard

deriving via Generically Wildcard instance Dupable Wildcard

deriving via Generically Wildcard instance Movable Wildcard

deriving via AsCopyableShow Wildcard instance Display Wildcard

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
            Control.<$> (unur PL.. Ur.lift (fromMaybe (error "buildDatabase: canonicalize failed")) Control.<$> canonicalize enode egraph)
            Control.<*> (unur Control.<$> unsafeFind egraph id)
    Control.pure PL.$
      Ur $
        fromRelations $
          PL.map (\(ENode args, id) -> MkRel {id, args}) nodes

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
  , universe :: !(HashSet EClassId)
  }
  deriving (Generic)

deriving instance (Show1 l) => Show (Database l)

universe :: Database l -> HashSet EClassId
universe = (.universe)

fromRelations :: (HasDatabase l) => [Relation l EClassId] -> Database l
fromRelations = foldr (\MkRel {id, args} -> insertDb id $ ENode args) newDatabase

newDatabase :: forall l. (HasDatabase l) => Database l
newDatabase = Database mempty mempty

toOperator :: forall l x. (Functor l) => l x -> Operator l
toOperator = Operator . (fmap (const Wildcard))

getTrie :: forall l. (HasDatabase l) => Operator l -> Database l -> Trie
getTrie l (Database db _) = HM.lookupDefault Trie.empty l db

insertDb :: forall l. (HasDatabase l) => EClassId -> ENode l -> Database l -> Database l
insertDb eid (ENode enode) =
  let row = F.toList $ MkRel {id = eid, args = enode}
   in #database . at (toOperator enode) %~ Just . maybe (Trie.singleton row) (Trie.insert row)
        >>> #universe %~ \universe -> foldl' (flip HS.insert) (HS.insert eid universe) enode

type HasDatabase l = (Hashable1 l, Functor l, Foldable l)
