{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Types.EGraph (
  EGraph (..),
  new,
  find,
  fromTerm,
  lookup,
  lookupEClass,
  unsafeFind,
  canonicalize,
  addNode,
  merges,
  merge,
  rebuild,
  Term,
  Equatable (..),
  hashconsL,
) where

import Control.Functor.Linear (StateT (..), asks, runReader, runStateT, void)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Monad.Borrow.Pure.Orphans (Movable1)
import Control.Monad.Borrow.Pure.Utils
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Coerce (Coercible, coerce)
import Data.Coerce.Directed (upcast)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses (EClasses, parents, setParents)
import Data.EGraph.Types.EClasses qualified as EC
import Data.EGraph.Types.ENode
import Data.EGraph.Types.Language
import Data.Fix (foldFixM)
import Data.Foldable1 (Foldable1, foldlM1)
import Data.Functor.Classes (Show1)
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear
import Data.HashMap.Mutable.Linear.Borrowed (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromJust)
import Data.Set.Mutable.Linear.Borrowed (Set)
import Data.Set.Mutable.Linear.Borrowed qualified as Set
import Data.UnionFind.Linear.Borrowed (UnionFind)
import Data.UnionFind.Linear.Borrowed qualified as UFB
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear qualified as Ur
import Debug.Trace.Linear qualified as DT
import GHC.Generics (Generic, Generically (..))
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

data EGraph l = EGraph
  { unionFind :: !UnionFind
  , classes :: !(EClasses l)
  , hashcons :: !(HashMap (ENode l) EClassId)
  , worklist :: !(Set EClassId)
  }
  deriving (Generic)

deriveGeneric ''EGraph

deriving via Generically (EGraph l) instance Consumable (EGraph l)

hashconsL :: RecordLabel (EGraph l) "hashcons" (HashMap (ENode l) EClassId)
hashconsL = #hashcons

fromTerm ::
  (P.Traversable l, Hashable1 l, Show1 l) =>
  Mut α (EGraph l) %1 ->
  Term l ->
  BO α (Ur (ENode l), Ur EClassId, Mut α (EGraph l))
fromTerm egraph term = Control.do
  (Ur node, egraph) <-
    flip runStateT egraph
      $ runUrT
      $ foldFixM
        ( \nodes ->
            ENode
              P.<$> P.traverse
                (\node -> UrT $ StateT \egraph -> addNode egraph node)
                nodes
        )
        term
  (Ur eid, egraph) <- addNode egraph node
  Control.pure (Ur node, Ur eid, egraph)

instance LinearOnly (EGraph l) where
  linearOnly :: LinearOnlyWitness (EGraph l)
  linearOnly = UnsafeLinearOnly

new :: (Hashable1 l) => Linearly %1 -> EGraph l
new = runReader Control.do
  unionFind <- asks UFB.empty
  classes <- asks $ EC.new
  hashcons <- asks $ HMB.empty 16
  worklist <- asks $ Set.empty 16
  Control.pure EGraph {..}

find :: Borrow k α (EGraph l) %1 -> EClassId -> BO α (Ur (Maybe EClassId))
find egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.find k uf

lookup :: (P.Traversable l, Hashable1 l) => ENode l -> Share α (EGraph l) %1 -> BO α (Ur (Maybe EClassId))
lookup enode egraph =
  move egraph & \(Ur egraph) -> runUrT $ runMaybeT do
    enode <- MaybeT $ UrT (canonicalize egraph enode)
    MaybeT $ UrT $ move . Data.fmap copy Control.<$> HMB.lookup enode (egraph .# #hashcons)

lookupEClass ::
  (Hashable1 l, Movable1 l) =>
  EClassId ->
  Borrow k α (EGraph l) %1 ->
  BO α (Ur (Maybe (NonEmpty (ENode l))))
lookupEClass eid egraph = Control.do
  let %1 clss = egraph .# #classes
  EC.nodes clss eid

class Equatable l a where
  equivalent :: Share α (EGraph l) -> a -> a -> BO α (Ur (Maybe Bool))

instance Equatable l EClassId where
  equivalent egraph eid1 eid2 = Control.do
    Ur eid1 <- find egraph eid1
    Ur eid2 <- find egraph eid2
    Control.pure $ Ur $ (P.==) P.<$> eid1 P.<*> eid2

instance (P.Traversable l, Hashable1 l) => Equatable l (ENode l) where
  equivalent egraph enode1 enode2 = Control.do
    Ur meid1 <- canonicalize egraph enode1
    Ur meid2 <- canonicalize egraph enode2
    Control.pure $ Ur $ (P.==) P.<$> meid1 P.<*> meid2

canonicalize :: (P.Traversable l) => Share α (EGraph l) %1 -> ENode l -> BO α (Ur (Maybe (ENode l)))
canonicalize egraph (ENode node) =
  move egraph & \(Ur egraph) -> Control.do
    let uf = egraph .# #unionFind
    runUrT $ coerce P.. P.sequenceA
      P.<$> P.mapM
        ( \eid ->
            UrT
              $ Data.fmap (coerceLin @_ @(Maybe EClassId))
              Control.<$> UFB.find (coerce eid) uf
        )
        node

unsafeFind :: Borrow k α (EGraph f) %1 -> EClassId -> BO α (Ur EClassId)
unsafeFind egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.unsafeFind k uf

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear coerce

addNode ::
  (P.Traversable l, Hashable1 l, Show1 l) =>
  Mut α (EGraph l) %1 ->
  ENode l ->
  BO α (Ur EClassId, Mut α (EGraph l))
addNode egraph enode = Control.do
  () <- DT.trace ("Adding node: " <> show enode) $ Control.pure ()
  (Ur mid, egraph) <- sharing egraph \egraph ->
    lookup enode egraph
  () <- DT.trace (" looked eid: " <> show mid) $ Control.pure ()
  case mid of
    Just eid -> Control.pure (Ur eid, egraph)
    Nothing -> Control.do
      () <- DT.trace "Node is new, creating new EClassId" $ Control.pure ()
      (Ur eid, egraph) <- reborrowing egraph \egraph -> Control.do
        (eid, uf) <- UFB.fresh (egraph .# #unionFind)
        Control.pure $ uf `lseq` Ur.lift EClassId eid
      () <- DT.trace (" created eid: " <> show eid) $ Control.pure ()
      egraph <- reborrowing_ egraph \egraph -> Control.do
        let %1 !classes = egraph .# #classes
        (Ur _, classes) <- EC.insertIfNew eid enode classes
        Control.pure $ consume classes
      () <- DT.trace " inserted into classes" $ Control.pure ()
      egraph <- reborrowing_ egraph \egraph -> Control.do
        Control.void $ HMB.insert enode eid (egraph .# #hashcons)
      () <- DT.trace " inserted into hashcons" $ Control.pure ()

      Control.pure (Ur eid, egraph)

merge ::
  EClassId ->
  EClassId ->
  Mut α (EGraph l) %1 ->
  BO α (Ur (Maybe EClassId), Mut α (EGraph l))
merge eid1 eid2 egraph = Control.do
  (Ur eids, egraph) <- sharing egraph \egraph -> Control.do
    Ur eid1 <- find egraph eid1
    Ur eid2 <- find egraph eid2
    Control.pure $ Ur $ (,) P.<$> eid1 P.<*> eid2
  case eids of
    Nothing -> Control.pure (Ur Nothing, egraph)
    Just (eid1, eid2) ->
      if eid1 == eid2
        then Control.pure (Ur (Just eid1), egraph)
        else Control.do
          (Ur eid, egraph) <- reborrowing egraph \egraph -> Control.do
            (eid, uf) <- UFB.unsafeUnion (coerce eid1) (coerce eid2) (egraph .# #unionFind)
            Control.pure $ uf `lseq` Ur.lift EClassId eid

          egraph <- reborrowing_ egraph \egraph -> Control.do
            Control.void $ Set.insert eid (egraph .# #worklist)

          Control.pure (Ur (Just eid), egraph)

merges ::
  (Foldable1 t) =>
  t EClassId ->
  Mut α (EGraph l) %1 ->
  BO α (Ur (Maybe EClassId), Mut α (EGraph l))
merges eids egraph = flip runStateT egraph
  $ runUrT
  $ runMaybeT do
    foldlM1 (\id1 id2 -> MaybeT $ UrT $ StateT $ merge id1 id2) eids

rebuild ::
  forall α l.
  (Hashable1 l, Movable1 l, P.Traversable l) =>
  Mut α (EGraph l) %1 ->
  BO α (Mut α (EGraph l))
rebuild = loop
  where
    loop :: Mut α (EGraph l) %1 -> BO α (Mut α (EGraph l))
    loop egraph = Control.do
      (Ur isNull, egraph) <- sharing egraph \e -> Set.null $ e .# #worklist
      if isNull
        then Control.do
          Control.pure egraph
        else Control.do
          (todos, egraph) <- reborrowing egraph \egraph -> Control.do
            todos <- Set.take_ (egraph .# #worklist)
            Control.pure $ Set.toListUnborrowed todos
          (todos, egraph) <- sharing egraph \egraph -> Control.do
            todos <-
              mapMaybe unur
                Control.<$> Data.mapM (\k -> move k & \(Ur k) -> find egraph k) todos
            Data.mapM (\k -> move k & \(Ur k) -> (Ur k,) Control.<$> parents (egraph .# #classes) k) todos
          egraph <- forRebor_ egraph todos \egraph (Ur eid, Ur ps) ->
            repair egraph eid ps
          loop egraph

repair ::
  (Hashable1 l, Movable1 l, P.Traversable l) =>
  Mut α (EGraph l) %1 ->
  EClassId ->
  [(ENode l, EClassId)] ->
  BO α ()
repair egraph eid parents = Control.do
  Ur parents <- Control.pure $ move $ map move parents
  egraph <- forRebor_ egraph parents $ \egraph (Ur (p_node, p_class)) -> Control.do
    egraph <- reborrowing_ egraph \egraph ->
      void $ HMB.delete p_node (egraph .# #hashcons)
    (Ur (fromJust -> p_node), egraph) <- sharing egraph \egraph ->
      canonicalize egraph p_node
    (Ur p_class, egraph) <- sharing egraph \egraph ->
      unsafeFind egraph p_class
    void $ HMB.insert p_node p_class (egraph .# #hashcons)
  (newParents, egraph) <- reborrowing' egraph \egraph -> Control.do
    (newPs, newPsLend) <- withLinearlyBO \lin -> Control.do
      ps <- withLinearlyBO $ Control.pure . HMB.empty @(ENode _) @EClassId 16
      Control.pure $ borrow ps lin
    (egraph, newPs) <- forRebor2_ egraph newPs parents
      $ \egraph newPs (Ur (p_node, p_class)) ->
        Control.do
          (Ur p_node, egraph) <- sharing egraph $ \egraph ->
            canonicalize egraph p_node
          (mem, newPs) <- sharing newPs \newPs ->
            Data.fmap copy Control.<$> HMB.lookup (fromJust p_node) newPs
          case mem of
            Just class' ->
              move class' & \(Ur class') ->
                void $ merge p_class class' egraph
            Nothing -> Control.pure $ consume egraph
          Control.pure $ consume newPs

    egraph `lseq` newPs `lseq` Control.pure (\end -> reclaim newPsLend (upcast end))

  void $ setParents eid newParents (egraph .# #classes)
