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
import Control.Lens (ifolded, withIndex)
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Utils
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (coerce)
import Data.Coerce.Directed (upcast)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses (setParents)
import Data.EGraph.Types.EClasses qualified as EC
import Data.EGraph.Types.EGraph.Internal
import Data.EGraph.Types.ENode
import Data.EGraph.Types.Term
import Data.Fix (foldFixM)
import Data.Foldable1 (Foldable1, foldlM1)
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue qualified as HMUr
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue.Frozen qualified as FHMUr
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe qualified as P
import Data.Record.Linear
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

getOriginalNode ::
  Borrow k α (EGraph d l) %m ->
  EClassId ->
  BO α (Ur (Maybe (ENode l)))
getOriginalNode egraph eid =
  share egraph & \(Ur egraph) ->
    HMUr.lookup eid (egraph .# #nodes)

addTerm ::
  (Analysis l d, Hashable1 l) =>
  Term l ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur (ENode l), Ur EClassId, Mut α (EGraph d l))
addTerm term egraph = Control.do
  (Ur node, egraph) <-
    flip runStateT egraph $
      runUrT $
        foldFixM
          ( \nodes ->
              ENode
                P.<$> P.traverse
                  (\node -> UrT $ StateT $ addCanonicalNode node)
                  nodes
          )
          term
  (Ur eid, egraph) <- addCanonicalNode node egraph
  Control.pure (Ur node, Ur eid, egraph)

new :: forall d l. (Hashable1 l) => Linearly %1 -> EGraph d l
new = runReader Control.do
  unionFind <- asks UFB.empty
  classes <- asks $ EC.new
  nodes <- asks $ HMUr.empty 2048
  hashcons <- asks $ HMUr.empty 2048
  worklist <- asks BUV.new
  Control.pure EGraph {..}

find :: Borrow k α (EGraph d l) %m -> EClassId -> BO α (Ur (Maybe EClassId))
find egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.find k uf

lookup :: (P.Traversable l, Hashable1 l) => ENode l -> Borrow bk α (EGraph d l) %m -> BO α (Ur (Maybe EClassId))
lookup enode egraph =
  share egraph & \(Ur egraph) -> runUrT $ runMaybeT do
    !enode <- MaybeT $ UrT (canonicalize enode egraph)
    MaybeT $ UrT $ HMUr.lookup enode (egraph .# #hashcons)

lookupTerm ::
  (P.Traversable l, Hashable1 l) =>
  Term l ->
  Borrow bk α (EGraph d l) %m ->
  BO α (Ur (Maybe EClassId))
lookupTerm term egraph =
  share egraph & \(Ur egraph) -> Control.do
    let go term =
          foldFixM
            (\t -> MaybeT $ UrT (lookup (ENode t) egraph))
            term
    runUrT $ runMaybeT (go term)

getAnalysis ::
  EClassId ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Maybe d))
getAnalysis eid egraph =
  share egraph & \(Ur egraph) -> runUrT $ runMaybeT do
    let clss = egraph .# #classes
    eid <- MaybeT $ UrT $ find egraph eid
    MaybeT $ UrT $ EC.lookupAnalysis clss eid

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

canonicalize ::
  (P.Traversable l) =>
  ENode l ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur (Maybe (ENode l)))
canonicalize (ENode node) egraph =
  share egraph & \(Ur egraph) -> Control.do
    let uf = egraph .# #unionFind
    runUrT $
      coerce P.. P.sequenceA
        P.<$> P.mapM
          ( \eid ->
              UrT $
                Data.fmap (coerceLin @_ @(Maybe EClassId))
                  Control.<$> UFB.find (coerce eid) uf
          )
          node

-- | Canonicalize a node, without checking the existence of eclass ids.
unsafeCanonicalize ::
  (P.Traversable l) =>
  ENode l ->
  Borrow bk α (EGraph d l) %m ->
  BO α (Ur (ENode l))
unsafeCanonicalize enode egraph =
  unsafeCanonicalize' enode (egraph .# #unionFind)

-- | A variant of 'unsafeCanonicalize' that uses underlying 'UnionFind'.
unsafeCanonicalize' ::
  (P.Traversable l) =>
  ENode l ->
  Borrow bk α UnionFind %m ->
  BO α (Ur (ENode l))
unsafeCanonicalize' (ENode node) uf =
  share uf & \(Ur uf) -> Control.do
    runUrT $
      coerce
        P.<$> P.mapM
          ( \eid ->
              UrT $
                Data.fmap (coerceLin @_ @(EClassId))
                  Control.<$> UFB.unsafeFind (coerce eid) uf
          )
          node

unsafeFind :: Borrow k α (EGraph d l) %m -> EClassId -> BO α (Ur EClassId)
unsafeFind egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.unsafeFind k uf

unsafeMakeAnalyzeNode ::
  (Analysis l d) =>
  ENode l ->
  Borrow k α (EGraph d l) %m ->
  BO α (Ur d)
unsafeMakeAnalyzeNode enode egraph =
  share egraph & \(Ur egraph) -> runUrT do
    let ecs = egraph .# #classes
    makeAnalysis P.<$> P.forM enode.unwrap \eid -> do
      eid <- UrT $ unsafeFind egraph eid
      (eid,) P.. P.fromJust P.<$> UrT (EC.lookupAnalysis ecs eid)

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
        void $ HMUr.insert enode eid (egraph .# #hashcons)
      egraph <- reborrowing_ egraph \egraph -> Control.do
        !dic <- HMUr.insert eid enode (egraph .# #nodes)
        Control.pure $! consume dic
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

      egraph <- reborrowing_ egraph \egraph -> Control.do
        void $ EC.unsafeMerge eid outdatedId $ egraph .# #classes

      egraph <- reborrowing_ egraph \egraph ->
        void $ BUV.push eid (egraph .# #worklist)

      Control.pure (Ur (Merged eid), egraph)

merges ::
  (Foldable1 t, P.Functor t, Movable1 l, Hashable1 l, Analysis l d) =>
  t EClassId ->
  Mut α (EGraph d l) %1 ->
  BO α (Ur (Maybe MergeResult), Mut α (EGraph d l))
merges eids egraph = flip runStateT egraph $
  runUrT $
    runMaybeT do
      foldlM1 (\id1 id2 -> P.fmap (id1 P.<>) $ MaybeT $ UrT $ StateT $ merge (getMergedId id1) (getMergedId id2)) $ P.fmap AlreadyMerged eids

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
        then Control.pure egraph
        else Control.do
          (Ur todos, egraph) <- reborrowing egraph \egraph -> Control.do
            todos <- BUV.takeOut_ (egraph .# #worklist)
            Control.pure (BUV.toList todos)
          (Ur todos, egraph) <- sharing egraph \egraph -> runUrT do
            nubHash
              P.<$> P.mapM (\k -> move k & \(Ur k) -> UrT $ unsafeFind egraph k) todos

          egraph <- forRebor_ egraph todos \egraph eid ->
            move eid & \(Ur eid) -> repair egraph eid
          loop egraph

repair ::
  (Hashable1 l, Movable1 l, Analysis l d) =>
  Mut α (EGraph d l) %1 ->
  EClassId ->
  BO α ()
repair egraph eid = Control.do
  (Ur numParents, egraph) <- sharing egraph \egraph -> Control.do
    mpare <- EC.lookupParents (egraph .# #classes) eid
    case mpare of
      -- FIXME: id MUST be present in classes - please review the invariant.
      Nothing -> Control.pure $ Ur 0
      Just pare -> HMUr.size pare
  egraph <- reborrowing_ egraph \egraph -> Control.do
    let %1 !(!hashcons, !classes, !uf) = DataFlow.do
          (hashcons, egraph) <- splitRecord egraph -# #hashcons
          (classes, egraph) <- egraph -# #classes
          uf <- egraph !# #unionFind
          (hashcons, classes, uf)
    Ur !parents <-
      share classes & \(Ur classes) -> Control.do
        mpare <- EC.lookupParents classes eid
        -- This is safe because the parents are not modified in this region
        FHMUr.unsafeFreeze . unur Control.<$> case mpare of
          Nothing ->
            -- FIXME: id MUST be present in classes - please review the invariant.

            asksLinearly \lin ->
              dup lin & \(lin, lin') ->
                share $ borrow_ (HMUr.empty 16 lin) lin'
          -- error $ "Impossible mpare None in Parents (divide): " <> P.show eid
          Just pare -> Control.pure $ share pare
    void $ iforRebor2_ hashcons uf parents \ !hashcons !uf !p_node !p_class -> Control.do
      -- NOTE:
      --    Seems like removing outdated node significantly worsens performance
      --    on some cases. Hence, as it doesn't affect soundness, we stop deleting it
      --    at the cost of some memory leakage.
      --    One alternative is to remove conditionally when the p_node is outdated,
      --    but that worsens performance in some cases by ~100x.

      -- !hashcons <- void . HMUr.delete p_node <%= hashcons
      (Ur !p_node, uf) <- {-# SCC "repair/loop1/unsafeCanon" #-} unsafeCanonicalize' p_node <$~ uf
      (Ur !p_class, uf) <- UFB.unsafeFind (coerce p_class) <$~ uf
      Control.pure (consume uf)
      void $ {-# SCC "update_hashcons/insert" #-} HMUr.insert p_node (coerce p_class) hashcons

  (Ur parents, egraph) <- sharing egraph \egraph -> Control.do
    -- FIXME: id MUST be present in classes - please review the invariant.
    !mps <- EC.lookupParents (egraph .# #classes) eid
    !ps <-
      {- copy
        . fromMaybe (error "Must be just") -}
      maybe (asksLinearly $ HMUr.empty 16) (Control.pure . copy) mps
    Control.pure $! FHMUr.freeze ps
  (newParents, egraph) <- reborrowing' egraph \egraph -> Control.do
    (newPs, newPsLend) <- asksLinearlyM \lin -> Control.do
      ps <- asksLinearly $ HMUr.empty @(ENode _) @EClassId numParents
      Control.pure $ borrow ps lin
    (egraph, newPs) <- forRebor2Of_ (ifolded P.. withIndex) egraph newPs parents $
      \egraph newPs ncs ->
        move ncs & \(Ur (p_node, p_class)) -> Control.do
          (Ur p_node, egraph) <- {-# SCC "repair/loop2/unsafeCanon" #-} unsafeCanonicalize p_node <$~ egraph
          (Ur mem, newPs) <- sharing newPs \newPs -> HMUr.lookup p_node newPs
          Ur newId <- case mem of
            Just class' ->
              move class' & \(Ur class') -> Control.do
                (Ur eid, egraph) <- unsafeMerge p_class class' egraph
                Control.pure $ egraph `lseq` Ur (getMergedId eid)
            Nothing -> unsafeFind egraph p_class
          Control.void $ {-# SCC "upwardMerge/insert" #-} HMUr.insert p_node newId newPs

    egraph <- newPs `lseq` reborrowing_ egraph (modifyAnalysis id eid)
    -- Rebuild analysis after modification
    (Ur ps, egraph) <- sharing egraph \egraph -> Control.do
      -- FIXME: id MUST be present in classes - please review the invariant.
      !mps <- EC.lookupParents (egraph .# #classes) eid
      !ps <-
        {- copy
          . fromMaybe (error "Must be just") -}
        maybe (asksLinearly $ HMUr.empty 16) (Control.pure . copy) mps
      Control.pure $! FHMUr.freeze ps
    void $ iforRebor_ egraph ps \egraph pNode pClass -> Control.do
      (newAnal, egraph) <- sharing egraph \egraph -> Control.do
        Ur analysis <- unsafeMakeAnalyzeNode pNode egraph
        Ur old <- EC.lookupAnalysis (egraph .# #classes) pClass
        let !d = P.maybe analysis (/\ analysis) old
        if Just d P.== old
          then Control.pure Nothing
          else Control.pure $ Just $ Ur d
      case newAnal of
        Nothing -> Control.pure $ consume egraph
        Just (Ur d) -> Control.do
          egraph <- reborrowing_ egraph \egraph -> Control.do
            void $ EC.setAnalysis pClass d (egraph .# #classes)
          !set <- {-# SCC "update_worklist/insert" #-} BUV.push pClass (egraph .# #worklist)
          Control.pure $ consume set

    Control.pure (\end -> reclaim newPsLend (upcast end))

  void $ setParents eid newParents (egraph .# #classes)

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
