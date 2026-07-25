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
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.Types.EGraph (
  EGraph (..),
  new,
  numEClasses,
  size,
  find,
  addTerm,
  getAnalysis,
  lookup,
  lookupTerm,
  lookupEClass,
  unsafeFind,
  canonicalize,
  unsafeCanonicalize,
  refill,
  addNode,
  addCanonicalNode,
  merges,
  merge,
  unsafeMerge,
  MergeResult (..),
  getMergedId,
  rebuild,
  Term,
  Equatable (..),
  hashconsL,
  Analysis (..),
) where

import Algebra.Semilattice
import Control.Functor.Linear (StateT (..), asks, runReader, runStateT, void)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Utils hiding ((:-))
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (coerce)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses qualified as EC
import Data.EGraph.Types.EGraph.Internal
import Data.EGraph.Types.EGraph.Refill (refill)
import Data.EGraph.Types.ENode
import Data.EGraph.Types.Term
import Data.Foldable qualified as F
import Data.Foldable1 (Foldable1, foldlM1)
import Data.Functor.Foldable (cataA)
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue qualified as HMUr
import Data.HashSet qualified as HS
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe qualified as P
import Data.Record.Linear.Borrow.Experimental.PatternMatch
import Data.Ref.Linear qualified as LRef
import Data.Ref.Linear.Borrow qualified as Ref
import Data.Traversable qualified as P
import Data.UnionFind.Linear.Borrowed (UnionFind)
import Data.UnionFind.Linear.Borrowed qualified as UFB
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Lifted (Movable1)
import GHC.Generics (Generic)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Prelude qualified as P

{-# INLINEABLE addTerm #-}
addTerm ::
  forall d l α.
  (Analysis l d, Hashable1 l) =>
  Term l ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur (ENode l), Ur EClassId, Mut α (EGraph d l))
addTerm term0 egraph = Control.do
  let !shape0 = unwrapTerm term0
  (Ur eids0, egraph) <- goChildren (F.toList shape0) [] egraph
  let !node0 = ENode (refill shape0 eids0)
  (Ur eid0, egraph) <- addCanonicalNode node0 egraph
  Control.pure (Ur node0, Ur eid0, egraph)
  where
    -- Direct BO-level recursion threading the e-graph explicitly instead of
    -- an UrT-over-StateT tower (cf. addNestedENode): no per-node transformer
    -- plumbing around the addCanonicalNode calls. Same post-order,
    -- left-to-right insertion sequence as the previous cataA fold.
    go :: Term l -> Mut α (EGraph d l) %1 -> BO α (Ur EClassId, Mut α (EGraph d l))
    go term egraph = Control.do
      let !shape = unwrapTerm term
      (Ur eids, egraph) <- goChildren (F.toList shape) [] egraph
      addCanonicalNode (ENode (refill shape eids)) egraph

    goChildren ::
      [Term l] ->
      [EClassId] ->
      Mut α (EGraph d l) %1 ->
      BO α (Ur [EClassId], Mut α (EGraph d l))
    goChildren [] acc egraph = Control.pure (Ur (P.reverse acc), egraph)
    goChildren (t : ts) acc egraph = Control.do
      (Ur eid, egraph) <- go t egraph
      goChildren ts (eid : acc) egraph

new :: forall d l. Linearly %1 -> EGraph d l
new = runReader Control.do
  unionFind <- asks UFB.empty
  classes <- asks $ EC.new
  hashcons <- asks $ HMUr.empty 2048
  worklist <- asks $ LRef.new []
  analysisWorklist <- asks $ LRef.new []
  nodeSetsCanonical <- asks $ LRef.new True
  Control.pure EGraph {..}

{-# INLINEABLE find #-}
find :: Borrow k α (EGraph d l) %m -> EClassId -> BO α (Ur (Maybe EClassId))
find egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.find k uf

{-# INLINEABLE lookup #-}
lookup :: (P.Traversable l, Hashable1 l) => ENode l -> Borrow bk α (EGraph d l) %m -> BO α (Ur (Maybe EClassId))
lookup enode egraph =
  share egraph & \(Ur egraph) -> runUrT $ runMaybeT do
    !enode <- MaybeT $ UrT (canonicalize enode egraph)
    MaybeT $ UrT $ HMUr.lookup enode (egraph .# #hashcons)

{-# INLINEABLE lookupTerm #-}
lookupTerm ::
  (P.Traversable l, Hashable1 l) =>
  Term l ->
  Borrow bk α (EGraph d l) %m ->
  BO α (Ur (Maybe EClassId))
lookupTerm term egraph =
  share egraph & \(Ur egraph) -> Control.do
    let go term =
          cataA
            ( \t -> do
                t <- P.sequenceA t
                MaybeT $ UrT (lookup (ENode t) egraph)
            )
            term
    runUrT $ runMaybeT (go term)

{-# INLINEABLE getAnalysis #-}
getAnalysis ::
  EClassId ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Maybe d))
getAnalysis eid egraph =
  share egraph & \(Ur egraph) -> runUrT $ runMaybeT do
    let clss = egraph .# #classes
    eid <- MaybeT $ UrT $ find egraph eid
    MaybeT $ UrT $ EC.lookupAnalysis clss eid

{-# INLINEABLE lookupEClass #-}
lookupEClass ::
  EClassId ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Maybe (NonEmpty (ENode l))))
lookupEClass eid egraph =
  share egraph & \(Ur egraph) -> Control.do
    Ur eid <- find egraph eid
    case eid of
      Nothing -> Control.pure $ Ur Nothing
      Just eid -> Control.do
        let %1 clss = egraph .# #classes
        EC.nodes clss eid

class Equatable l a where
  equivalent :: Share α (EGraph d l) -> a -> a -> BO α (Ur (Maybe Bool))

instance Equatable l EClassId where
  equivalent egraph eid1 eid2 = Control.do
    Ur eid1 <- find egraph eid1
    Ur eid2 <- find egraph eid2
    Control.pure $ Ur $ (P.==) P.<$> eid1 P.<*> eid2

instance (P.Traversable l, Hashable1 l) => Equatable l (ENode l) where
  equivalent egraph enode1 enode2 = Control.do
    Ur meid1 <- lookup enode1 egraph
    Ur meid2 <- lookup enode2 egraph
    Control.pure $ Ur $ (P.==) P.<$> meid1 P.<*> meid2

instance (P.Traversable l, Hashable1 l) => Equatable l (Term l) where
  equivalent egraph term1 term2 = Control.do
    Ur meid1 <- lookupTerm term1 egraph
    Ur meid2 <- lookupTerm term2 egraph
    Control.pure $ Ur $ (P.==) P.<$> meid1 P.<*> meid2

{-# INLINEABLE canonicalize #-}
canonicalize ::
  forall l d k α m.
  (P.Traversable l) =>
  ENode l ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Maybe (ENode l)))
canonicalize (ENode node) egraph =
  share egraph & \(Ur egraph) -> Control.do
    let uf = egraph .# #unionFind
        -- Direct recursion over the children instead of a UrT-wrapped
        -- traversal: no per-child transformer plumbing.
        go :: [EClassId] -> [EClassId] -> BO α (Ur (Maybe (ENode l)))
        go [] acc =
          Control.pure $! Ur $! Just $! ENode (refill node (P.reverse acc))
        go (eid : rest) acc = Control.do
          Ur meid <- UFB.find (coerce eid) uf
          case meid of
            Nothing -> Control.pure (Ur Nothing)
            Just eid' -> go rest (coerce eid' : acc)
    go (F.toList node) []

-- | Canonicalize a node, without checking the existence of eclass ids.
{-# INLINEABLE unsafeCanonicalize #-}
unsafeCanonicalize ::
  (P.Traversable l) =>
  ENode l ->
  Borrow bk α (EGraph d l) %m ->
  BO α (Ur (ENode l))
unsafeCanonicalize enode egraph =
  unsafeCanonicalize' enode (egraph .# #unionFind)

-- | A variant of 'unsafeCanonicalize' that uses underlying 'UnionFind'.
{-# INLINEABLE unsafeCanonicalize' #-}
unsafeCanonicalize' ::
  forall l bk α m.
  (P.Traversable l) =>
  ENode l ->
  Borrow bk α UnionFind %m ->
  BO α (Ur (ENode l))
unsafeCanonicalize' (ENode node) uf =
  share uf & \(Ur uf) -> Control.do
    let go :: [EClassId] -> [EClassId] -> BO α (Ur (ENode l))
        go [] acc =
          Control.pure $! Ur $! ENode (refill node (P.reverse acc))
        go (eid : rest) acc = Control.do
          Ur k <- UFB.unsafeFind (coerce eid) uf
          go rest (coerce k : acc)
    go (F.toList node) []

{-# INLINEABLE unsafeFind #-}
unsafeFind :: Borrow k α (EGraph d l) %m -> EClassId -> BO α (Ur EClassId)
unsafeFind egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.unsafeFind k uf

{-# INLINEABLE unsafeMakeAnalyzeNode #-}
unsafeMakeAnalyzeNode ::
  forall l d k α m.
  (Analysis l d) =>
  ENode l ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur d)
unsafeMakeAnalyzeNode enode egraph =
  share egraph & \(Ur egraph) -> Control.do
    let ecs = egraph .# #classes
        -- Direct recursion over the children instead of a UrT-wrapped
        -- traversal: no per-child transformer plumbing.
        go :: [EClassId] -> [(EClassId, d)] -> BO α (Ur d)
        go [] acc =
          Control.pure $! Ur $! makeAnalysis $! refill enode.unwrap (P.reverse acc)
        go (eid : rest) acc = Control.do
          Ur eid <- unsafeFind egraph eid
          Ur manal <- EC.lookupAnalysis ecs eid
          go rest ((eid, P.fromJust manal) : acc)
    go (children enode) []

{-# INLINEABLE addNode #-}
addNode ::
  (Analysis l d, Hashable1 l) =>
  Mut α (EGraph d l) %1 ->
  ENode l ->
  BO α (Ur (Maybe EClassId), Mut α (EGraph d l))
addNode egraph node = Control.do
  (node, egraph) <- canonicalize node <$~ egraph
  case node of
    Ur Nothing -> Control.pure (Ur Nothing, egraph)
    Ur (Just enode) ->
      Bi.first (Ur.lift Just) Control.<$> addCanonicalNode enode egraph

{-# INLINEABLE addCanonicalNode #-}
addCanonicalNode ::
  (Hashable1 l, Analysis l d) =>
  ENode l ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur EClassId, Mut α (EGraph d l))
addCanonicalNode enode egraph = Control.do
  (Ur prepared, egraph) <- sharing egraph \egraph ->
    HMUr.lookupForInsert enode (egraph .# #hashcons)
  case prepared of
    Left eid -> Control.pure (Ur eid, egraph)
    Right insertPlan -> Control.do
      (Ur eid, egraph) <- reborrowing egraph \egraph -> Control.do
        (eid, uf) <- UFB.fresh (egraph .# #unionFind)
        Control.pure $ uf `lseq` Ur.lift EClassId eid
      egraph <- reborrowing_ egraph \egraph -> Control.do
        (Ur !d, egraph) <- sharing egraph $ unsafeMakeAnalyzeNode enode
        -- Parent edges must be registered under CANONICAL child ids: a
        -- modifyAnalysis hook may have merged a child's class away since the
        -- node was canonicalized (mid-batch), and a stale id would miss the
        -- class table and silently drop the edge, leaving later congruence
        -- repair incomplete.
        (Ur childIds, egraph) <- sharing egraph \egraph ->
          share egraph & \(Ur egraph) -> Control.do
            Ur ids <- move Control.<$> Data.mapM (\c -> move c & \(Ur c) -> unsafeFind egraph c) (children enode)
            Control.pure $ Ur $ P.map (\(Ur c) -> c) ids
        -- The class node SET stores the canonical form (egg's classes hold
        -- canonicalized nodes; the hashcons key deliberately keeps the
        -- as-given form). They differ only when a modifyAnalysis merge made
        -- a child id stale mid-batch.
        let !rawChildren = children enode
            !setNode =
              if childIds P.== rawChildren
                then enode
                else ENode (refill (unwrap enode) childIds)
        void $ EC.unsafeInsertNew eid setNode childIds d $ egraph .# #classes
      egraph <- reborrowing_ egraph \egraph -> Control.do
        let %1 !(!hashcons, !worklist) = egraph .@ (#hashcons, #worklist)
        -- The hashcons table has not changed since 'lookupForInsert', so resume
        -- that probe at its recorded miss instead of hashing and probing the
        -- structured node a second time.
        hashcons <- HMUr.unsafeInsertPrepared insertPlan eid hashcons
        worklist <- Ref.modify (Ur (eid, enode) :) worklist
        Control.pure $ hashcons `lseq` consume worklist
      egraph <- modifyAnalysis id eid <%= egraph

      Control.pure (Ur eid, egraph)

data MergeResult = Merged {-# UNPACK #-} !EClassId | AlreadyMerged {-# UNPACK #-} !EClassId
  deriving (P.Show, P.Eq, P.Ord, Generic)

instance P.Semigroup MergeResult where
  Merged eid <> AlreadyMerged {} = Merged eid
  AlreadyMerged {} <> Merged eid = Merged eid
  AlreadyMerged _ <> AlreadyMerged eid2 = AlreadyMerged eid2
  Merged _ <> Merged eid2 = Merged eid2

getMergedId :: MergeResult -> EClassId
getMergedId (Merged eid) = eid
getMergedId (AlreadyMerged eid) = eid

{-# INLINEABLE merge #-}
merge ::
  (Movable1 l, Hashable1 l, Analysis l d) =>
  EClassId ->
  EClassId ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur (Maybe MergeResult), Mut α (EGraph d l))
merge eid1 eid2 egraph = Control.do
  (eidsThere, egraph) <- sharing egraph \egraph -> Control.do
    let uf = egraph .# #unionFind
    Ur eid1 <- UFB.member (coerce eid1) uf
    Ur eid2 <- UFB.member (coerce eid2) uf
    Control.pure $ eid1 && eid2
  if not eidsThere
    then Control.pure (Ur Nothing, egraph)
    else Control.do
      (Ur !resl, !egraph) <- unsafeMerge eid1 eid2 egraph
      Control.pure (Ur (Just resl), egraph)

{-# INLINEABLE unsafeMerge #-}
unsafeMerge ::
  forall l d α.
  (Movable1 l, Hashable1 l, Analysis l d) =>
  EClassId ->
  EClassId ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur MergeResult, Mut α (EGraph d l))
unsafeMerge eid1 eid2 egraph = Control.do
  (Ur (eid1, eid2), egraph) <- sharing egraph \egraph -> Control.do
    Ur eid1 <- unsafeFind egraph eid1
    Ur eid2 <- unsafeFind egraph eid2
    Control.pure $ Ur (eid1, eid2)
  if eid1 == eid2
    then Control.do
      Control.pure (Ur (AlreadyMerged eid1), egraph)
    else Control.do
      -- Histories must be snapshotted here, BEFORE EC.unsafeMerge: after the
      -- merge the leader's ref holds the concatenation, and a post-merge read
      -- would enqueue the loser's parents twice.
      (Ur (eid, outdatedId, leaderParents, subParents), egraph) <- sharing egraph \egraph -> Control.do
        Ur (size1, history1) <- EC.lookupParentHistoryWithCount (egraph .# #classes) eid1
        Ur (size2, history2) <- EC.lookupParentHistoryWithCount (egraph .# #classes) eid2
        -- hegg chooses the class with more parents, with ties going to
        -- the first argument. Representative choice affects canonical
        -- e-nodes, so union-by-rank is not trajectory-equivalent here.
        Control.pure $ Ur $ if size1 < size2 then (eid2, eid1, history2, history1) else (eid1, eid2, history1, history2)
      egraph <- reborrowing_ egraph \egraph -> Control.do
        (Ur actualLeader, uf) <- UFB.unsafeUnionTo (coerce eid) (coerce outdatedId) (egraph .# #unionFind)
        Control.pure $ case actualLeader of
          _ -> consume uf

      (Ur analChanges, egraph) <- reborrowing egraph \egraph -> Control.do
        (changes, clss) <- EC.unsafeMerge eid outdatedId $ egraph .# #classes
        Control.pure $ clss `lseq` changes

      egraph <- reborrowing_ egraph \egraph -> Control.do
        let %1 !(!wl, !awl, !setsCanon) = egraph .@ (#worklist, #analysisWorklist, #nodeSetsCanonical)
        -- Parent histories are already in worklist orientation: the spines
        -- flow through unchanged (egg's pending.extend(parents)).
        wl <- Ref.modify (subParents <>) wl
        let (leaderChanged, subChanged) = analChanges
            pending =
              (if subChanged then subParents else [])
                <> (if leaderChanged then leaderParents else [])
        awl <- Ref.modify (pending <>) awl
        setsCanon <- Ref.modify (`lseq` False) setsCanon
        Control.pure (consume wl `lseq` consume awl `lseq` consume setsCanon)

      egraph <- reborrowing_ egraph (modifyAnalysis id eid)

      Control.pure (Ur (Merged eid), egraph)

{-# INLINEABLE merges #-}
merges ::
  (Foldable1 t, P.Functor t, Movable1 l, Hashable1 l, Analysis l d) =>
  t EClassId ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur (Maybe MergeResult), Mut α (EGraph d l))
merges eids egraph = flip runStateT egraph $
  runUrT $
    runMaybeT do
      foldlM1 (\id1 id2 -> P.fmap (id1 P.<>) $ MaybeT $ UrT $ StateT $ merge (getMergedId id1) (getMergedId id2)) $ P.fmap AlreadyMerged eids

{-# INLINEABLE rebuild #-}
rebuild ::
  forall α d l.
  (Hashable1 l, Movable1 l, Analysis l d) =>
  Mut α (EGraph d l) %1 ->
  BO α (Mut α (EGraph d l))
rebuild = loop HS.empty
  where
    loop :: HS.HashSet EClassId -> Mut α (EGraph d l) %1 -> BO α (Mut α (EGraph d l))
    loop !touched egraph = Control.do
      (Ur (rawTodos, rawAnalysisTodos), egraph) <- reborrowing egraph \egraph -> Control.do
        let %1 !(!worklist, !analysisWorklist) = egraph .@ (#worklist, #analysisWorklist)
        (Ur todos, worklist) <- Ref.update (\todos -> Control.pure (move todos, [])) worklist
        (Ur analysisTodos, analysisWorklist) <-
          Ref.update (\todos -> Control.pure (move todos, [])) analysisWorklist
        Control.pure $
          consume worklist `lseq`
            consume analysisWorklist `lseq`
              Ur (todos, analysisTodos)
      if P.null rawTodos && P.null rawAnalysisTodos
        then
          if HS.null touched
            then Control.pure egraph
            else Control.do
              -- egg's rebuild_classes: canonicalize + deduplicate the node set
              -- of every class touched by this rebuild, then mark all node
              -- sets canonical so database builds can trust them without
              -- re-canonicalizing every row. Touched ids are re-found at the
              -- fixpoint: a batch-time canonical owner may have been merged
              -- away (and deleted from the class table) by a later batch.
              (Ur owners, egraph) <- sharing egraph \egraph ->
                share egraph & \(Ur egraph) -> Control.do
                  Ur ids <-
                    move
                      Control.<$> Data.mapM
                        (\c -> move c & \(Ur c) -> unsafeFind egraph c)
                        (HS.toList touched)
                  Control.pure $ Ur $ HS.toList $ HS.fromList $ P.map (\(Ur c) -> c) ids
              egraph <- forReborrowing_ egraph owners \egraph owner ->
                move owner & \(Ur owner) -> trimClass egraph owner
              egraph <- reborrowing_ egraph \egraph -> Control.do
                flag <- Ref.modify (`lseq` True) (egraph .# #nodeSetsCanonical)
                Control.pure $ consume flag
              Control.pure egraph
        else Control.do
          (Ur todos, egraph) <- sharing egraph \egraph -> runUrT do
            canonical <- P.mapM (canonicalTodo egraph) rawTodos
            UrT $ Control.pure $ Ur (P.reverse (nubHash canonical))

          egraph <- forReborrowing_ egraph todos \egraph todo ->
            move todo & \(Ur (pClass, pNode)) -> repair egraph pClass pNode

          -- Match hegg's rebuild cadence: the analysis batch is the one
          -- snapshotted before congruence repair. Work enqueued by either
          -- phase is handled by the next recursive batch.
          -- Deduplicate analysis repairs on the (owner, node) PAIR — egg's
          -- analysis_pending is a UniqueQueue of (node, class) pairs. hegg
          -- instead keeps only the newest entry per owner (nubIntOn fst),
          -- which silently drops sibling parent nodes of the same class:
          -- an analysis improvement discoverable only through a dropped
          -- node is then never propagated, leaving maintained analyses
          -- stale (observed: ExtractBest cost 15 vs true 13; see the
          -- "maintained ExtractBest equals post-hoc" reproducer).
          (Ur analysisTodos, egraph) <- sharing egraph \egraph -> runUrT do
            canonical <- P.mapM (canonicalAnalysisTodo egraph) rawAnalysisTodos
            UrT $ Control.pure $ Ur (P.reverse (nubHash canonical))

          egraph <- forReborrowing_ egraph analysisTodos \egraph todo ->
            move todo & \(Ur (pClass, pNode)) -> repairAnal egraph pClass pNode
          loop (P.foldl' (\s (c, _) -> HS.insert c s) touched todos) egraph

    -- Rewrite one class's node set with canonicalized, deduplicated nodes
    -- (egg's rebuild_classes body). A missing class (merged away between
    -- re-find and trim cannot happen — ids are re-found at the fixpoint with
    -- no merges pending — but tolerate it defensively).
    trimClass :: forall β. Mut β (EGraph d l) %1 -> EClassId -> BO β ()
    trimClass egraph owner = Control.do
      (Ur mnodes, egraph) <- sharing egraph \egraph ->
        EC.nodes (egraph .# #classes) owner
      case mnodes of
        Nothing -> Control.pure $ consume egraph
        Just ns -> Control.do
          (Ur canonSet, egraph) <- sharing egraph \egraph ->
            share egraph & \(Ur egraph) -> Control.do
              Ur ns' <-
                move
                  Control.<$> Data.mapM
                    (\nd -> move nd & \(Ur nd) -> unsafeCanonicalize nd egraph)
                    (F.toList ns)
              Control.pure $ Ur $ HS.fromList $ P.map (\(Ur nd) -> nd) ns'
          egraph <- reborrowing_ egraph \egraph ->
            void $ EC.setNodes owner canonSet (egraph .# #classes)
          Control.pure $ consume egraph

    canonicalTodo egraph (Ur (pClass, pNode)) = UrT $ Control.do
      Ur pClass <- unsafeFind egraph pClass
      Ur pNode <- unsafeCanonicalize pNode egraph
      Control.pure $ Ur (pClass, pNode)

    canonicalAnalysisTodo egraph (Ur (pClass, pNode)) = UrT $ Control.do
      Ur pClass <- unsafeFind egraph pClass
      Control.pure $ Ur (pClass, pNode)

{-# INLINEABLE repair #-}
repair ::
  (Hashable1 l, Movable1 l, Analysis l d) =>
  Mut α (EGraph d l) %1 ->
  EClassId ->
  ENode l ->
  BO α ()
repair egraph p_class p_node = Control.do
  -- Congruence repair, faithful to egg/hegg's 'repair'. Iterate a frozen
  -- snapshot of this class's parents (a merge inside the loop mutates the
  -- classes map, so iterating the live map is unsafe) and, per parent,
  -- re-canonicalise the node and re-establish the hashcons invariant. The
  -- GLOBAL hashcons doubles as hegg's @insertLookupNM@: inserting the canonical
  -- @(node -> owning class)@ returns the previous binding, and if that previous
  -- class differs from the current one the two are congruent and get merged
  -- (which re-queues the survivor, so 'rebuild' loops to a fixpoint).
  --
  -- We deliberately do NOT rebuild/overwrite this class's parent set. Parent
  -- sets are maintained solely by 'merge' (it unions a subsumed class's parents
  -- into the survivor); rebuilding them from the snapshot would silently drop
  -- any parent added by a merge performed WHILE this repair runs, leaving the
  -- same canonical node in two classes — a congruence violation that inflated
  -- the e-graph. hegg maintains parents the same union-only way. Stale
  -- (pre-canonical) hashcons and parent keys are kept: it is sound (reads always
  -- 'find'/canonicalise) and pruning them measurably worsens performance.
  (Ur prev, egraph) <- reborrowing egraph \egraph -> Control.do
    (Ur prev, hc) <- {-# SCC "update_hashcons/insert" #-} HMUr.insert p_node p_class (egraph .# #hashcons)
    Control.pure (hc `lseq` Ur prev)
  case prev of
    Just other -> Control.do
      (Ur oc, egraph) <- flip unsafeFind other <$~ egraph
      if oc P.== p_class
        then Control.pure (consume egraph)
        else Control.do
          -- hegg's repair calls @merge existing_class repair_id@.  Argument
          -- order is observable because equal parent counts retain the first
          -- class as leader.
          (Ur _res, egraph) <- {-# SCC "upwardMerge/merge" #-} unsafeMerge oc p_class egraph
          Control.pure (consume egraph)
    Nothing -> Control.pure (consume egraph)

{- | Analysis counterpart of 'repair': called (from 'rebuild') for classes
whose analysis value changed. Runs the analysis-driven modification hook for
the class itself, then recomputes the analyses of its parents, propagating
further changes through the analysis worklist.
-}
{-# INLINEABLE repairAnal #-}
repairAnal ::
  (Analysis l d) =>
  Mut α (EGraph d l) %1 ->
  EClassId ->
  ENode l ->
  BO α ()
repairAnal egraph pClass pNode = Control.do
  (Ur newAnal, egraph) <- sharing egraph \egraph -> Control.do
    Ur analysis <- unsafeMakeAnalyzeNode pNode egraph
    Ur old <- EC.lookupAnalysis (egraph .# #classes) pClass
    let !d = P.maybe analysis (/\ analysis) old
    if Just d P.== old
      then Control.pure $ Ur Nothing
      else Control.pure $ Ur (Just d)
  case newAnal of
    Nothing -> Control.pure $ consume egraph
    Just d -> Control.do
      egraph <- reborrowing_ egraph \egraph -> Control.do
        void $ EC.setAnalysis pClass d (egraph .# #classes)
      (Ur parents, egraph) <- sharing egraph \egraph -> Control.do
        Ur history <- EC.lookupParentHistory (egraph .# #classes) pClass
        Control.pure (Ur history)
      egraph <- reborrowing_ egraph \egraph -> Control.do
        awl <- Ref.modify (parents <>) (egraph .# #analysisWorklist)
        Control.pure $ consume awl
      modifyAnalysis id pClass egraph

numEClasses :: Borrow k α (EGraph d l) %m -> BO α (Ur Int)
numEClasses egraph = Control.do
  let clss = egraph .# #classes
  EC.size clss

-- | # of (raw) e-nodes in the e-graph.
size :: Borrow k α (EGraph d l) %m -> BO α (Ur Int)
{-# INLINE size #-}
size egraph =
  share egraph & \(Ur egraph) -> Control.do
    HMUr.size (egraph .# #hashcons)
