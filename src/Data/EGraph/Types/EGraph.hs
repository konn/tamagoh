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
import Control.Monad.Borrow.Pure.Experimental.Borrows
import Control.Monad.Borrow.Pure.Experimental.Loop (iforReborrowingOf_)
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
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue.Frozen qualified as FHMUr
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe qualified as P
import Data.Record.Linear.Borrow.Experimental.PatternMatch
import Data.Traversable qualified as P
import Data.UnionFind.Linear.Borrowed (UnionFind)
import Data.UnionFind.Linear.Borrowed qualified as UFB
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Lifted (Movable1)
import Data.Vector.Unboxed.Mutable.Growable.Borrowed qualified as BUV
import GHC.Generics (Generic)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Prelude qualified as P

{-# INLINEABLE getOriginalNode #-}
getOriginalNode ::
  Borrow k α (EGraph d l) %m ->
  EClassId ->
  BO α (Ur (Maybe (ENode l)))
getOriginalNode egraph eid =
  share egraph & \(Ur egraph) ->
    HMUr.lookup eid (egraph .# #nodes)

{-# INLINEABLE addTerm #-}
addTerm ::
  (Analysis l d, Hashable1 l) =>
  Term l ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur (ENode l), Ur EClassId, Mut α (EGraph d l))
addTerm term egraph = Control.do
  (Ur node, egraph) <-
    flip runStateT egraph $
      runUrT $
        cataA
          ( \nodes ->
              P.fmap ENode
                P.. P.traverse
                  (\node -> UrT $ StateT $ addCanonicalNode node)
                P.=<< P.sequenceA nodes
          )
          term
  (Ur eid, egraph) <- addCanonicalNode node egraph
  Control.pure (Ur node, Ur eid, egraph)

new :: forall d l. Linearly %1 -> EGraph d l
new = runReader Control.do
  unionFind <- asks UFB.empty
  classes <- asks $ EC.new
  nodes <- asks $ HMUr.empty 2048
  hashcons <- asks $ HMUr.empty 2048
  worklist <- asks BUV.new
  analysisWorklist <- asks BUV.new
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
  (Ur mid, egraph) <- lookup enode <$~ egraph
  case mid of
    Just eid -> Control.pure (Ur eid, egraph)
    Nothing -> Control.do
      (Ur eid, egraph) <- reborrowing egraph \egraph -> Control.do
        (eid, uf) <- UFB.fresh (egraph .# #unionFind)
        Control.pure $ uf `lseq` Ur.lift EClassId eid
      egraph <- reborrowing_ egraph \egraph -> Control.do
        (Ur !d, egraph) <- sharing egraph $ unsafeMakeAnalyzeNode enode
        void $ EC.insertIfNew eid enode d $ egraph .# #classes
      egraph <- reborrowing_ egraph \egraph -> Control.do
        let %1 !(!hashcons, !nodes) = egraph .@ (#hashcons, #nodes)
        -- Both keys are freshly absent (the 'lookup' above returned Nothing,
        -- and 'eid' is a just-'fresh'ed union-find id) and neither insert's
        -- old value is used, so route through the plain 'alter': it skips the
        -- 'Swapper'/'Ur' old-value plumbing that 'insert' builds (a hot-path
        -- cost — ~5% alloc in the flat profile).
        hashcons <- HMUr.alter (\_ -> Just eid) enode hashcons
        nodes <- HMUr.alter (\_ -> Just enode) eid nodes
        Control.pure $ hashcons `lseq` consume nodes
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
      (Ur eid, egraph) <- reborrowing egraph \egraph -> Control.do
        (eid, uf) <- UFB.union (coerce eid1) (coerce eid2) (egraph .# #unionFind)
        Control.pure $ uf `lseq` Ur.lift EClassId (fromMaybe (error "union failed in EGraph.merge") Data.<$> eid)

      -- Recover Hashcons invariant. This is not mentioned in the original egg paper,
      -- but seems necessary to keep the hashcons invariant correct.
      -- Incorporating this into rebuild seems possible, but for simplicity,
      -- we do it here for now.
      let outdatedId
            | eid == eid1 = eid2
            | otherwise = eid1
      egraph <- reborrowing_ egraph \egraph -> Control.do
        (Ur node, egraph) <- sharing egraph \egraph -> Control.do
          Ur node <- getOriginalNode egraph outdatedId
          unsafeCanonicalize (fromMaybe (error "unsafeMerge: getOriginalNode failed") node) egraph
        void $ HMUr.insert node eid (egraph .# #hashcons)

      (Ur analChanged, egraph) <- reborrowing egraph \egraph -> Control.do
        (changed, clss) <- EC.unsafeMerge eid outdatedId $ egraph .# #classes
        Control.pure $ clss `lseq` changed

      egraph <- reborrowing_ egraph \egraph -> Control.do
        let %1 !(!wl, !awl) = egraph .@ (#worklist, #analysisWorklist)
        void $ BUV.push eid wl
        -- If the meet changed the winner's analysis, its parents need
        -- re-analysis (egg's analysis_pending discipline).
        if analChanged
          then void $ BUV.push eid awl
          else Control.pure (consume awl)

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
rebuild = loop
  where
    loop :: Mut α (EGraph d l) %1 -> BO α (Mut α (EGraph d l))
    loop egraph = Control.do
      (Ur isNull, egraph) <- sharing egraph \e -> BUV.null $ e .# #worklist
      if isNull
        then Control.do
          -- Congruence is restored; propagate pending analysis changes
          -- to parents (egg's analysis_pending discipline).
          (Ur isANull, egraph) <- sharing egraph \e -> BUV.null $ e .# #analysisWorklist
          if isANull
            then Control.pure egraph
            else Control.do
              (Ur todos, egraph) <- reborrowing egraph \egraph -> Control.do
                todos <- BUV.takeOut_ (egraph .# #analysisWorklist)
                Control.pure (BUV.toList todos)
              (Ur todos, egraph) <- sharing egraph \egraph -> runUrT do
                nubHash
                  P.<$> P.mapM (\k -> move k & \(Ur k) -> UrT $ unsafeFind egraph k) todos

              egraph <- forReborrowing_ egraph todos \egraph eid ->
                move eid & \(Ur eid) -> repairAnal egraph eid
              loop egraph
        else Control.do
          (Ur todos, egraph) <- reborrowing egraph \egraph -> Control.do
            todos <- BUV.takeOut_ (egraph .# #worklist)
            Control.pure (BUV.toList todos)
          (Ur todos, egraph) <- sharing egraph \egraph -> runUrT do
            nubHash
              P.<$> P.mapM (\k -> move k & \(Ur k) -> UrT $ unsafeFind egraph k) todos

          egraph <- forReborrowing_ egraph todos \egraph eid ->
            move eid & \(Ur eid) -> repair egraph eid
          loop egraph

{-# INLINEABLE repair #-}
repair ::
  (Hashable1 l, Movable1 l, Analysis l d) =>
  Mut α (EGraph d l) %1 ->
  EClassId ->
  BO α ()
repair egraph eid = Control.do
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
  (Ur parents, egraph) <- sharing egraph \egraph -> Control.do
    -- FIXME: id MUST be present in classes - please review the invariant.
    !mps <- EC.lookupParents (egraph .# #classes) eid
    maybe
      (asksLinearly $ FHMUr.empty 16)
      (Control.fmap FHMUr.freeze . clone)
      mps
  void $
    iforReborrowingOf_ FHMUr.foldFrozen egraph parents $
      \egraph p_node p_class ->
        move (p_node, p_class) & \(Ur (p_node, p_class)) -> Control.do
          (Ur p_node, egraph) <- {-# SCC "repair/unsafeCanon" #-} unsafeCanonicalize p_node <$~ egraph
          (Ur p_class, egraph) <- flip unsafeFind p_class <$~ egraph
          (Ur prev, egraph) <- reborrowing egraph \egraph -> Control.do
            (Ur prev, hc) <- {-# SCC "update_hashcons/insert" #-} HMUr.insert p_node p_class (egraph .# #hashcons)
            Control.pure (hc `lseq` Ur prev)
          case prev of
            Just other -> Control.do
              (Ur oc, egraph) <- flip unsafeFind other <$~ egraph
              if oc P.== p_class
                then Control.pure (consume egraph)
                else Control.do
                  (Ur _res, egraph) <- {-# SCC "upwardMerge/merge" #-} unsafeMerge p_class other egraph
                  Control.pure (consume egraph)
            Nothing -> Control.pure (consume egraph)

{- | Analysis counterpart of 'repair': called (from 'rebuild') for classes
whose analysis value changed. Runs the analysis-driven modification hook for
the class itself, then recomputes the analyses of its parents, propagating
further changes through the analysis worklist.
-}
{-# INLINEABLE repairAnal #-}
repairAnal ::
  (Movable1 l, Analysis l d) =>
  Mut α (EGraph d l) %1 ->
  EClassId ->
  BO α ()
repairAnal egraph eid = Control.do
  egraph <- reborrowing_ egraph (modifyAnalysis id eid)
  (Ur ps, egraph) <- sharing egraph \egraph -> Control.do
    !mps <- EC.lookupParents (egraph .# #classes) eid
    !ps <- maybe (asksLinearly $ HMUr.empty 16) clone mps
    Control.pure $! FHMUr.freeze ps
  void $ iforReborrowingOf_ FHMUr.foldFrozen egraph ps \egraph pNode pClass ->
    move (pNode, pClass) & \(Ur (pNode, pClass)) ->
      Control.do
        (newAnal, egraph) <- sharing egraph \egraph -> Control.do
          Ur pClass <- unsafeFind egraph pClass
          Ur analysis <- unsafeMakeAnalyzeNode pNode egraph
          Ur old <- EC.lookupAnalysis (egraph .# #classes) pClass
          let !d = P.maybe analysis (/\ analysis) old
          if Just d P.== old
            then Control.pure Nothing
            else Control.pure $ Just $ Ur (pClass, d)
        case newAnal of
          Nothing -> Control.pure $ consume egraph
          Just (Ur (pClass, d)) -> Control.do
            egraph <- reborrowing_ egraph \egraph -> Control.do
              void $ EC.setAnalysis pClass d (egraph .# #classes)
            !set <- {-# SCC "update_analysis_worklist/insert" #-} BUV.push pClass (egraph .# #analysisWorklist)
            Control.pure $ consume set

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
