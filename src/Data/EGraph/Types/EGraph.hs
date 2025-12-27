{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Types.EGraph (
  EGraph,
  find,
  lookup,
  unsafeFind,
  canonicalize,
  add,
  merge,
  rebuild,
) where

import Control.Functor.Linear (StateT (..), runStateT, void)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Monad.Borrow.Pure.Orphans (Movable1)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Coerce (Coercible, coerce)
import Data.Coerce.Directed (upcast)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses (EClasses, parents, setParents)
import Data.EGraph.Types.EClasses qualified as EC
import Data.EGraph.Types.ENode
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear
import Data.HashMap.Mutable.Linear.Borrowed (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.Hashable.Lifted (Hashable1)
import Data.Maybe (fromJust)
import Data.Set.Mutable.Linear.Borrowed (Set)
import Data.Set.Mutable.Linear.Borrowed qualified as Set
import Data.UnionFind.Linear (UnionFind)
import Data.UnionFind.Linear qualified as UF
import Data.UnionFind.Linear.Borrowed qualified as UFB
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear qualified as Ur
import GHC.Generics (Generic)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

data EGraph f = EGraph
  { unionFind :: !UnionFind
  , classes :: !(EClasses f)
  , hashcons :: !(HashMap (ENode f) EClassId)
  , worklist :: !(Set EClassId)
  }
  deriving (Generic)

instance LinearOnly (EGraph f) where
  linearOnly :: LinearOnlyWitness (EGraph f)
  linearOnly = UnsafeLinearOnly

find :: Borrow k α (EGraph f) %1 -> EClassId -> BO α (Maybe (Ur EClassId))
find egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.find k uf

lookup :: (P.Traversable l, Hashable1 l) => ENode l -> Share α (EGraph l) %1 -> BO α (Ur (Maybe EClassId))
lookup enode egraph =
  move egraph & \(Ur egraph) -> runUrT $ runMaybeT do
    enode <- MaybeT $ UrT (canonicalize egraph enode)
    MaybeT $ UrT $ move . Data.fmap copy Control.<$> HMB.lookup enode (egraph .# #hashcons)

canonicalize :: (P.Traversable l) => Share α (EGraph f) %1 -> ENode l -> BO α (Ur (Maybe (ENode l)))
canonicalize egraph (ENode node) =
  move egraph & \(Ur egraph) -> Control.do
    let uf = egraph .# #unionFind
    runUrT $ coerce P.. P.sequenceA
      P.<$> P.mapM
        ( \eid ->
            UrT
              $ maybe (Ur Nothing) (Ur.lift (Just P.. EClassId))
              Control.<$> UFB.find (coerce eid) uf
        )
        node

unsafeFind :: Borrow k α (EGraph f) %1 -> EClassId -> BO α (Ur EClassId)
unsafeFind egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.unsafeFind k uf

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear coerce

add ::
  (P.Traversable l, Hashable1 l) =>
  ENode l ->
  Mut α (EGraph l) %1 ->
  BO α (Ur EClassId, Mut α (EGraph l))
add enode egraph = Control.do
  (Ur mid, egraph) <- sharing egraph \egraph ->
    lookup enode egraph
  case mid of
    Just eid -> Control.pure (Ur eid, egraph)
    Nothing -> Control.do
      (Ur eid, egraph) <- reborrowing egraph \egraph -> Control.do
        (eid, uf) <- UFB.fresh (egraph .# #unionFind)
        Control.pure $ uf `lseq` Ur.lift EClassId eid
      egraph <- reborrowing_ egraph \egraph -> Control.do
        let %1 !classes = egraph .# #classes
        (Ur _, classes) <- EC.insertIfNew eid enode classes
        Control.pure $ consume classes

      Control.pure (Ur eid, egraph)

merge ::
  EClassId ->
  EClassId ->
  Mut α (EGraph l) %1 ->
  BO α (Ur (Maybe EClassId), Mut α (EGraph l))
merge eid1 eid2 egraph = Control.do
  (Ur eids, egraph) <- sharing egraph \egraph -> Control.do
    Ur eid1 <- maybe (Ur Nothing) (Data.fmap Just) Control.<$> find egraph eid1
    Ur eid2 <- maybe (Ur Nothing) (Data.fmap Just) Control.<$> find egraph eid2
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
        then Control.pure egraph
        else Control.do
          (todos, egraph) <- reborrowing egraph \egraph -> Control.do
            (todos, works) <- Set.take (egraph .# #worklist)
            Control.pure $ works `lseq` Set.toListUnborrowed todos
          (todos, egraph) <- sharing egraph \egraph -> Control.do
            todos <- catMaybes Control.<$> Data.mapM (\k -> find egraph k) todos
            Data.mapM (\(Ur k) -> (Ur k,) Control.<$> parents (egraph .# #classes) k) todos
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
    (Ur (fromJust -> p_node), egraph) <- sharing egraph \egraph -> canonicalize egraph p_node
    (Ur p_class, egraph) <- sharing egraph $ \egraph ->
      unsafeFind egraph p_class
    void $ HMB.insert p_node p_class (egraph .# #hashcons)
  (newParents, egraph) <- reborrowing' egraph \egraph -> Control.do
    (newPs, newPsLend) <- withLinearlyBO \lin -> Control.do
      ps <- HMB.empty @(ENode _) @EClassId 16
      Control.pure $ borrow ps lin
    (egraph, newPs) <- forRebor2_ egraph newPs parents
      $ \egraph newPs (Ur (p_node, p_class)) ->
        Control.do
          (Ur p_node, egraph) <- sharing egraph $ \egraph ->
            canonicalize egraph p_node
          (mem, newPs) <- sharing newPs \newPs ->
            Data.fmap copy Control.<$> HMB.lookup (fromJust p_node) newPs
          case mem of
            Just class' -> void $ merge p_class class' egraph
            Nothing -> Control.pure $ consume egraph
          Control.pure $ consume newPs

    egraph `lseq` newPs `lseq` Control.pure (\end -> reclaim newPsLend (upcast end))

  void $ setParents eid newParents (egraph .# #classes)

forRebor ::
  (Data.Traversable t) =>
  Mut α a %1 ->
  t b %1 ->
  (forall β. Mut (β /\ α) a %1 -> b %1 -> BO (β /\ α) c) ->
  BO α (t c, Mut α a)
{-# INLINE forRebor #-}
forRebor bor tb k = flip runStateT bor Control.do
  Data.forM tb \b -> StateT \bor -> Control.do
    reborrowing bor \bor -> Control.do
      k bor b

forRebor2 ::
  (Data.Traversable t) =>
  Mut α a %1 ->
  Mut α b %1 ->
  t c %1 ->
  ( forall β.
    Mut (β /\ α) a %1 ->
    Mut (β /\ α) b %1 ->
    c %1 ->
    BO (β /\ α) d
  ) ->
  BO α (t d, (Mut α a, Mut α b))
{-# INLINE forRebor2 #-}
forRebor2 bor bor' tb k = flip runStateT (bor, bor') Control.do
  Data.forM tb \b -> StateT \(bor, bor') -> Control.do
    (\((a, b), c) -> (a, (c, b))) Control.<$> reborrowing bor \bor -> Control.do
      reborrowing bor' \bor' -> assocRBO $ k (assocBorrowL $ upcast bor) (assocBorrowL $ upcast bor') b

forRebor_ ::
  (Data.Traversable t, Consumable (t ())) =>
  Mut α a %1 ->
  t b %1 ->
  (forall β. Mut (β /\ α) a %1 -> b %1 -> BO (β /\ α) ()) ->
  BO α (Mut α a)
{-# INLINE forRebor_ #-}
forRebor_ bor tb k = Control.fmap (uncurry lseq) $ forRebor bor tb k

forRebor2_ ::
  (Data.Traversable t, Consumable (t ())) =>
  Mut α a %1 ->
  Mut α b %1 ->
  t c %1 ->
  ( forall β.
    Mut (β /\ α) a %1 ->
    Mut (β /\ α) b %1 ->
    c %1 ->
    BO (β /\ α) ()
  ) ->
  BO α (Mut α a, Mut α b)
{-# INLINE forRebor2_ #-}
forRebor2_ bor bor' tb k = Control.fmap (uncurry lseq) $ forRebor2 bor bor' tb k
