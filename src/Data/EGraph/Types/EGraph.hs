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
  addTerm,
  lookup,
  lookupEClass,
  unsafeFind,
  canonicalize,
  unsafeCanonicalize,
  addNode,
  merges,
  merge,
  unsafeMerge,
  MergeResult (..),
  getMergedId,
  rebuild,
  Term,
  Equatable (..),
  hashconsL,
) where

import Control.Functor.Linear (StateT (..), asks, runReader, runStateT, void)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Monad.Borrow.Pure.Utils
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (coerce)
import Data.Coerce.Directed (upcast)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses (EClasses, parents, setParents)
import Data.EGraph.Types.EClasses qualified as EC
import Data.EGraph.Types.ENode
import Data.EGraph.Types.Term
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
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)
import GHC.Generics (Generic, Generically (..))
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Text.Show.Borrowed (Display)
import Prelude qualified as P

{- | Invariant: all the 'EClassId's appearing somewhere in this structure
  must be valid keys in the 'unionFind' field.
-}
data EGraph l = EGraph
  { unionFind :: !UnionFind
  -- ^ A union-find structure on e-class ids.
  , classes :: !(EClasses l)
  {- ^ A mapping from EClassId to EClass.

  Invariant: only the canonical EClassIds resides in the e-class.
  -}
  , nodes :: !(HashMap EClassId (ENode l))
  {- ^ A map from eclass-id to the _original_ enode.
  Associated e-node MUST BE canonical AFTER rebuilding.

  NOTE: this field is not mentioned in the original egg paper,
  but it is needed to recover the hashcons invariant on the nodes
  that are being unioned.
  -}
  , hashcons :: !(HashMap (ENode l) EClassId)
  {- ^
  A map from _canonical_ enodes to eclass-ids.
  Keys MUST BE canonical AFTER rebuilding.
  -}
  , worklist :: !(Set EClassId)
  -- ^ A set of eclass-ids that need to be repaired.
  }
  deriving (Generic)

deriveGeneric ''EGraph

deriving via
  Generically (EGraph l)
  instance
    (Copyable1 l, Show1 l) => Display (EGraph l)

deriving via Generically (EGraph l) instance Consumable (EGraph l)

deriving via Generically (EGraph l) instance (Movable1 l) => Dupable (EGraph l)

hashconsL :: RecordLabel (EGraph l) "hashcons" (HashMap (ENode l) EClassId)
hashconsL = #hashcons

getOriginalNode ::
  (Copyable1 l, Movable1 l) =>
  Borrow k α (EGraph l) %1 ->
  EClassId ->
  BO α (Ur (Maybe (ENode l)))
getOriginalNode egraph eid =
  share egraph & \(Ur egraph) -> Control.do
    maybe (Ur Nothing) (move . Just . copy) Control.<$> HMB.lookup eid (egraph .# #nodes)

addTerm ::
  (P.Traversable l, Hashable1 l, Movable1 l) =>
  Mut α (EGraph l) %1 ->
  Term l ->
  BO α (Ur (ENode l), Ur EClassId, Mut α (EGraph l))
addTerm egraph term = Control.do
  (Ur node, egraph) <-
    flip runStateT egraph
      $ runUrT
      $ foldFixM
        ( \nodes ->
            ENode
              P.<$> P.traverse
                (\node -> UrT $ StateT \egraph -> addCanonicalNode egraph node)
                nodes
        )
        term
  (Ur eid, egraph) <- addCanonicalNode egraph node
  Control.pure (Ur node, Ur eid, egraph)

instance LinearOnly (EGraph l) where
  linearOnly :: LinearOnlyWitness (EGraph l)
  linearOnly = UnsafeLinearOnly

new :: (Hashable1 l) => Linearly %1 -> EGraph l
new = runReader Control.do
  unionFind <- asks UFB.empty
  classes <- asks $ EC.new
  nodes <- asks $ HMB.empty 16
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
    !enode <- MaybeT $ UrT (canonicalize egraph enode)
    MaybeT $ UrT $ move . Data.fmap copy Control.<$> HMB.lookup enode (egraph .# #hashcons)

lookupEClass ::
  (Movable1 l) =>
  EClassId ->
  Borrow k α (EGraph l) %1 ->
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
  equivalent :: Share α (EGraph l) -> a -> a -> BO α (Ur (Maybe Bool))

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

-- | Canonicalize a node, without checking the existence of eclass ids.
unsafeCanonicalize :: (P.Traversable l) => Share α (EGraph l) %1 -> ENode l -> BO α (Ur (ENode l))
unsafeCanonicalize egraph (ENode node) =
  move egraph & \(Ur egraph) -> Control.do
    let uf = egraph .# #unionFind
    runUrT $ coerce
      P.<$> P.mapM
        ( \eid ->
            UrT
              $ Data.fmap (coerceLin @_ @(EClassId))
              Control.<$> UFB.unsafeFind (coerce eid) uf
        )
        node

unsafeFind :: Borrow k α (EGraph f) %1 -> EClassId -> BO α (Ur EClassId)
unsafeFind egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.unsafeFind k uf

addNode ::
  (P.Traversable l, Hashable1 l, Movable1 l) =>
  Mut α (EGraph l) %1 ->
  ENode l ->
  BO α (Ur (Maybe EClassId), Mut α (EGraph l))
addNode egraph node = Control.do
  (node, egraph) <- sharing egraph \egraph -> canonicalize egraph node
  case node of
    Ur Nothing -> Control.pure (Ur Nothing, egraph)
    Ur (Just enode) ->
      Bi.first (Ur.lift Just) Control.<$> addCanonicalNode egraph enode

addCanonicalNode ::
  (P.Traversable l, Hashable1 l, Movable1 l) =>
  Mut α (EGraph l) %1 ->
  ENode l ->
  BO α (Ur EClassId, Mut α (EGraph l))
addCanonicalNode egraph enode = Control.do
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
      egraph <- reborrowing_ egraph \egraph -> Control.do
        Control.void $ HMB.insert enode eid (egraph .# #hashcons)
      egraph <- reborrowing_ egraph \egraph -> Control.do
        !dic <- HMB.insert eid enode (egraph .# #nodes)
        Control.pure $! consume dic

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
  (Copyable1 l, Movable1 l, Hashable1 l, P.Traversable l) =>
  EClassId ->
  EClassId ->
  Mut α (EGraph l) %1 ->
  BO α (Ur (Maybe MergeResult), Mut α (EGraph l))
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
  (Copyable1 l, Movable1 l, Hashable1 l, P.Traversable l) =>
  EClassId ->
  EClassId ->
  Mut α (EGraph l) %1 ->
  BO α (Ur MergeResult, Mut α (EGraph l))
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
          unsafeCanonicalize egraph $ fromJust node
        void $ HMB.insert node eid (egraph .# #hashcons)

      egraph <- reborrowing_ egraph \egraph -> Control.do
        !set <- Set.inserts [eid] (egraph .# #worklist)
        Control.pure $! consume set

      Control.pure (Ur (Merged eid), egraph)

merges ::
  (Foldable1 t, P.Functor t, Copyable1 l, Movable1 l, Hashable1 l, P.Traversable l) =>
  t EClassId ->
  Mut α (EGraph l) %1 ->
  BO α (Ur (Maybe MergeResult), Mut α (EGraph l))
merges eids egraph = flip runStateT egraph
  $ runUrT
  $ runMaybeT do
    foldlM1 (\id1 id2 -> P.fmap (id1 P.<>) $ MaybeT $ UrT $ StateT $ merge (getMergedId id1) (getMergedId id2)) $ P.fmap AlreadyMerged eids

rebuild ::
  forall α l.
  (Hashable1 l, Movable1 l, P.Traversable l, Copyable1 l) =>
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
          (Ur todos, egraph) <- reborrowing egraph \egraph -> Control.do
            todos <- Set.take_ (egraph .# #worklist)
            Control.pure $ move $ Set.toListUnborrowed todos
          (todos, egraph) <- sharing egraph \egraph -> Control.do
            Ur todos <-
              Ur.lift nubHash
                . move
                . mapMaybe unur
                Control.<$> Data.mapM (\k -> move k & \(Ur k) -> find egraph k) todos
            Data.mapM
              ( \k ->
                  move k & \(Ur k) ->
                    (Ur k,) Control.<$> parents (egraph .# #classes) k
              )
              todos
          egraph <- forRebor_ egraph todos \egraph (Ur eid, Ur ps) ->
            repair egraph eid ps
          loop egraph

repair ::
  (Hashable1 l, Movable1 l, P.Traversable l, Copyable1 l) =>
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
      Data.fmap (fromMaybe (error "EGraph.repair: find failed")) Control.<$> find egraph p_class
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
