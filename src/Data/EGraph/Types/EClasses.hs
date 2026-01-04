{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.Types.EClasses (
  EClasses (),
  EClass (),
  analyses,
  new,
  lookupAnalysis,
  setAnalysis,
  nodes,
  delete,
  parents,
  setParents,
  addParent,
  find,
  member,
  insertIfNew,
  merge,
  unsafeMerge,
  size,
) where

import Algebra.Semilattice
import Control.Functor.Linear (void)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses.Internal
import Data.EGraph.Types.EGraph.Internal (Analysis (..))
import Data.EGraph.Types.ENode
import Data.Foldable (Foldable)
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear
import Data.HashMap.Mutable.Linear.Borrowed (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.HashMap.Strict qualified as PHM
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe.Linear
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.Set.Mutable.Linear.Borrowed qualified as Set
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Lifted (Movable1)
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe

analyses ::
  (Movable d, Copyable d, Movable1 l, Hashable1 l) =>
  Borrow bk α (EClasses d l) %m ->
  BO α (Ur (PHM.HashMap EClassId ([ENode l], d)))
analyses clss =
  share clss & \(Ur clss) -> Control.do
    dic <- HMB.toBorrowList (coerceLin clss :: Share _ (Raw _ _))
    Ur.lift PHM.fromList
      . move
      Control.<$> Data.mapM
        ( \(Ur k, bor) ->
            move bor & \(Ur bor) -> Control.do
              nodes <- Set.toList (bor .# #nodes)
              Ur anal <- Data.fmap copy Control.<$> readSharedRef (bor .# #analysis)
              Control.pure (k, (nodes, anal))
        )
        dic

lookupAnalysis ::
  forall bk α d l m.
  (Copyable d) =>
  Borrow bk α (EClasses d l) %m ->
  EClassId ->
  BO α (Ur (Maybe d))
lookupAnalysis classes eid =
  share classes & \(Ur classes) -> Control.do
    let %1 clss = coerceLin classes :: Share α (Raw d l)
    mclass <- HMB.lookup eid clss
    case mclass of
      Nothing -> Control.pure (Ur Nothing)
      Just eclass -> Control.do
        Ur a <- readSharedRef (eclass .# #analysis)
        Control.pure (Ur (Just $ copy a))

setAnalysis ::
  forall α d l.
  (Consumable d) =>
  EClassId ->
  d ->
  Mut α (EClasses d l) %1 ->
  BO α (Ur Bool)
setAnalysis eid d classes = Control.do
  let %1 clss = coerceLin classes :: Mut α (Raw d l)
  mclass <- HMB.lookup eid clss
  case mclass of
    Nothing -> Control.pure $ Ur False
    Just eclass -> Control.do
      ref <- modifyRef (`lseq` d) $ eclass .# #analysis
      Control.pure $ ref `lseq` Ur True

parents ::
  forall bk α d l m.
  Borrow bk α (EClasses d l) %m ->
  EClassId ->
  BO α (Ur [(ENode l, EClassId)])
parents clss0 eid = Control.do
  let %1 clss = coerceLin clss0 :: Borrow bk α (Raw d l)
  mclass <- HMB.lookup eid clss
  case mclass of
    Nothing -> Control.pure (Ur [])
    Just eclass -> HMB.toList (eclass .# #parents)

delete ::
  forall α d l.
  Mut α (EClasses d l) %1 ->
  EClassId ->
  BO α (Maybe (EClass d l), Mut α (EClasses d l))
delete clss eid = Control.do
  let %1 !clss' = coerceLin clss :: Mut _ (Raw d l)
  Bi.second coerceLin Control.<$> HMB.delete eid clss'

nodes ::
  forall bk α d l m.
  (Movable1 l) =>
  Borrow bk α (EClasses d l) %m ->
  EClassId ->
  BO α (Ur (Maybe (NonEmpty (ENode l))))
nodes clss0 eid = Control.do
  let %1 clss = coerceLin clss0 :: Borrow bk α (Raw d l)
  mclass <- HMB.lookup eid clss
  case mclass of
    Nothing -> Control.pure (Ur Nothing)
    Just eclass -> Control.do
      Ur ns <- move Control.<$> Set.toList (eclass .# #nodes)
      Control.pure $ Ur (NonEmpty.nonEmpty ns)

setParents ::
  forall d l α.
  (Hashable1 l) =>
  EClassId ->
  HashMap (ENode l) EClassId %1 ->
  Mut α (EClasses d l) %1 ->
  BO α (Mut α (EClasses d l))
setParents eid ps clss = Control.do
  reborrowing_ clss \clss0 -> Control.do
    let %1 !clss = coerceLin clss0 :: Mut _ (Raw d l)
    mclass <- HMB.lookup eid clss
    case mclass of
      Nothing -> Control.pure $ consume ps
      Just eclass -> Control.do
        void $ HMB.swap ps (eclass .# #parents)

addParent ::
  (Hashable1 l) =>
  EClassId ->
  ENode l ->
  Mut α (EClass d l) %1 ->
  BO α (Mut α (EClass d l))
addParent pid enode eclass = Control.do
  eclass <- reborrowing_ eclass \eclass -> Control.do
    let %1 !parentsSet = eclass .# #parents
    void $ HMB.insert enode pid parentsSet
  Control.pure eclass

member ::
  forall d l bk α m.
  EClassId ->
  Borrow bk α (EClasses d l) %m ->
  BO α (Ur Bool)
member eid clss0 =
  share clss0 & \(Ur clss0) -> Control.do
    let clss = coerceLin clss0 :: Share _ (Raw d l)
    HMB.member eid clss

{- |
Returns 'True' if the node was newly inserted;
otherwise no change will be made and returns 'False'.
-}
insertIfNew ::
  forall d l α.
  (Hashable1 l, Foldable l, Consumable d) =>
  EClassId ->
  ENode l ->
  d ->
  Mut α (EClasses d l) %1 ->
  BO α (Ur Bool, Mut α (EClasses d l))
insertIfNew eid enode analysis clss = Control.do
  (Ur mem, clss) <- member eid <$~ clss
  if mem
    then Control.pure (Ur False, coerceLin clss)
    else Control.do
      nodes <- asksLinearly $ Set.singleton enode
      parents <- asksLinearly $ HMB.empty 16
      analysis <- asksLinearly $ Ref.new analysis
      (mop, clss) <- HMB.insert eid EClass {parents, nodes, analysis} $ coerceLin clss
      clss <- reborrowing_ clss \clss -> Control.do
        chss <-
          mapMaybe (\(Ur _, e) -> e)
            Control.<$> HMB.lookups (children enode) clss
        void $ Data.forM chss \ch -> addParent eid enode ch
      mop `lseq` Control.pure (Ur True, coerceLin clss)

{- | @'unsafeMerge' eid1 eid2 class@ merges the e-classes identified by @eid1@ and @eid2@, returning 'False' if the classes were already merged and no change will be made..
  Your must pass the canonical id as @eid1@, and the non-canonical id as @eid2@.
-}
merge ::
  (Hashable1 l, Movable1 l, Analysis l d) =>
  EClassId ->
  EClassId ->
  Mut α (EClasses d l) %1 ->
  BO α (Ur Bool, Mut α (EClasses d l))
merge eid1 eid2 clss = Control.do
  (Ur mem1, clss) <- member eid1 <$~ clss
  (Ur mem2, clss) <- member eid2 <$~ clss
  if not mem1 || not mem2
    then Control.pure (Ur False, clss)
    else (Ur True,) Control.<$> unsafeMerge eid1 eid2 clss

{- | @'unsafeMerge' eid1 eid2 class@ merges the e-classes identified by @eid1@ and @eid2@, without cheking the exitence of the eids.
  Your must pass the canonical id as @eid1@, and the non-canonical id as @eid2@.
-}
unsafeMerge ::
  forall α d l.
  ( Hashable1 l
  , Movable1 l
  , Analysis l d
  ) =>
  EClassId ->
  EClassId ->
  Mut α (EClasses d l) %1 ->
  BO α (Mut α (EClasses d l))
unsafeMerge eid1 eid2 clss
  | eid1 == eid2 = Control.pure clss
  | otherwise = Control.do
      (mr, clss) <- delete clss eid2
      let %1 !EClass {nodes = !rnodes, parents = !rparents, analysis = !ra} = case mr of
            Nothing -> error "EGraph.Types.EClasses.unsafeMerge: eid2 not found"
            Just eclass -> eclass
      let %1 !(Ur ranalysis) = move $ freeRef ra
      clss <- reborrowing_ clss \clss0 -> Control.do
        let clss = coerceLin clss0 :: Mut _ (Raw d l)
        l <- HMB.lookup eid1 clss
        case l of
          Nothing -> Control.pure $ rnodes `lseq` rparents `lseq` ()
          Just l -> Control.do
            (lnodes, l) <- reborrowing l \l -> Set.take_ (l .# #nodes)
            let %1 !nodes = Set.union lnodes rnodes

            (lparents, l) <- reborrowing l \l -> HMB.take_ (l .# #parents)
            let %1 !parents = HMB.union lparents rparents
            l <- reborrowing_ l \l -> Control.do
              void $ modifyRef (\la -> move la & \(Ur la) -> la /\ ranalysis) (l .# #analysis)

            l <- reborrowing_ l \l -> Control.do
              void $ Set.swap nodes (l .# #nodes)
            Control.void $ reborrowing_ l \l -> Control.do
              void $ HMB.swap parents $ l .# #parents

      Control.pure clss

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear \ !a -> coerce a

size :: Borrow k α (EClasses d l) %m -> BO α (Ur Int)
size = HMB.size . coerceLin
