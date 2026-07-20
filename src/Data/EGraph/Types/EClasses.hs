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
  lookupParentHistory,
  lookupParentHistoryWithCount,
  setAnalysis,
  nodes,
  delete,
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
import Control.Monad.Borrow.Pure.BO.Unsafe (Alias (..))
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses.Internal
import Data.EGraph.Types.EGraph.Internal (Analysis (..))
import Data.EGraph.Types.ENode
import Data.Foldable (Foldable)
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.HashMap.Strict qualified as PHM
import Data.HashSet qualified as PHS
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe.Linear
import Data.Record.Linear.Borrow.Experimental.PatternMatch
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow qualified as Ref
import Data.Unrestricted.Linear qualified as Ur
import Data.Unrestricted.Linear.Lifted (Movable1)
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

{-# INLINEABLE analyses #-}
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
              Ur (UnsafeAlias (Ur nodes)) <- Ref.readShare (bor .# #nodes)
              Ur anal <- Data.fmap copy Control.<$> Ref.readShare (bor .# #analysis)
              Control.pure (k, (PHS.toList nodes, anal))
        )
        dic

{-# INLINEABLE lookupParentHistory #-}
lookupParentHistory ::
  forall bk α d l m.
  Borrow bk α (EClasses d l) %m ->
  EClassId ->
  BO α (Ur [Ur (ENode l, EClassId)])
lookupParentHistory classes eid =
  share classes & \(Ur classes) -> Control.do
    let %1 clss = coerceLin classes :: Share α (Raw d l)
    mclass <- HMB.lookup eid clss
    case mclass of
      Nothing -> Control.pure (Ur [])
      Just eclass -> Control.do
        Ur (UnsafeAlias history) <- Ref.readShare (eclass .# #parentHistory)
        Control.pure (Ur history)

{-# INLINEABLE lookupParentHistoryWithCount #-}
lookupParentHistoryWithCount ::
  forall bk α d l m.
  Borrow bk α (EClasses d l) %m ->
  EClassId ->
  BO α (Ur (Int, [Ur (ENode l, EClassId)]))
lookupParentHistoryWithCount classes eid =
  share classes & \(Ur classes) -> Control.do
    let %1 clss = coerceLin classes :: Share α (Raw d l)
    mclass <- HMB.lookup eid clss
    case mclass of
      Nothing -> Control.pure (Ur (0, []))
      Just eclass -> Control.do
        let %1 !(!parentCount, !parentHistory) = eclass .@ (#parentCount, #parentHistory)
        Ur (UnsafeAlias !count) <- Ref.readShare parentCount
        Ur (UnsafeAlias history) <- Ref.readShare parentHistory
        Control.pure (Ur (count, history))

{-# INLINEABLE lookupAnalysis #-}
lookupAnalysis ::
  forall bk α d l m.
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
        Ur (UnsafeAlias !a) <- Ref.readShare (eclass .# #analysis)
        Control.pure (Ur (Just a))

{-# INLINEABLE setAnalysis #-}
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
      ref <- Ref.modify (`lseq` d) $ eclass .# #analysis
      Control.pure $ ref `lseq` Ur True

{-# INLINEABLE delete #-}
delete ::
  forall α d l.
  Mut α (EClasses d l) %1 ->
  EClassId ->
  BO α (Maybe (EClass d l), Mut α (EClasses d l))
delete clss eid = Control.do
  let %1 !clss' = coerceLin clss :: Mut _ (Raw d l)
  Bi.second coerceLin Control.<$> HMB.delete eid clss'

{-# INLINEABLE nodes #-}
nodes ::
  forall bk α d l m.
  Borrow bk α (EClasses d l) %m ->
  EClassId ->
  BO α (Ur (Maybe (NonEmpty (ENode l))))
nodes clss0 eid = Control.do
  let %1 clss = coerceLin clss0 :: Borrow bk α (Raw d l)
  mclass <- HMB.lookup eid clss
  case mclass of
    Nothing -> Control.pure (Ur Nothing)
    Just eclass ->
      share eclass & \(Ur eclass) -> Control.do
        Ur (UnsafeAlias (Ur ns)) <- Ref.readShare (eclass .# #nodes)
        Control.pure $ Ur $ NonEmpty.nonEmpty $ PHS.toList ns

{-# INLINEABLE addParent #-}
addParent ::
  EClassId ->
  ENode l ->
  Mut α (EClass d l) %1 ->
  BO α (Mut α (EClass d l))
addParent pid enode eclass = Control.do
  addParentN 1 pid enode eclass

{-# INLINEABLE addParentN #-}
addParentN ::
  Int ->
  EClassId ->
  ENode l ->
  Mut α (EClass d l) %1 ->
  BO α (Mut α (EClass d l))
addParentN multiplicity pid enode eclass = Control.do
  eclass <- reborrowing_ eclass \eclass -> Control.do
    let %1 !(!parentHistory, !parentCount) = eclass .@ (#parentHistory, #parentCount)
    parentHistory <- Ref.modify (P.replicate multiplicity (Ur (enode, pid)) <>) parentHistory
    (Ur (), parentCount) <-
      Ref.update
        ( \count ->
            move count & \(Ur count) ->
              Control.pure (Ur (), multiplicity P.+ count)
        )
        parentCount
    Control.pure (consume parentHistory `lseq` consume parentCount)
  Control.pure eclass

{-# INLINEABLE member #-}
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
{-# INLINEABLE insertIfNew #-}
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
      nodes <- asksLinearly $ Ref.new (Ur (PHS.singleton enode))
      parentHistory <- asksLinearly $ Ref.new []
      parentCount <- asksLinearly $ Ref.new 0
      analysis <- asksLinearly $ Ref.new analysis
      (mop, clss) <- HMB.insert eid EClass {parentHistory, parentCount, nodes, analysis} $ coerceLin clss
      clss <- reborrowing_ clss \clss -> Control.do
        chss <-
          mapMaybe (\(Ur child, e) -> consume child `lseq` e)
            Control.<$> HMB.lookupsAll (children enode) clss
        void $ Data.forM chss $ addParent eid enode
      mop `lseq` Control.pure (Ur True, coerceLin clss)

{- | @'unsafeMerge' eid1 eid2 class@ merges the e-classes identified by @eid1@ and @eid2@, returning 'False' if the classes were already merged and no change will be made..
  Your must pass the canonical id as @eid1@, and the non-canonical id as @eid2@.
-}
{-# INLINEABLE merge #-}
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
    else Control.do
      (Ur _changed, clss) <- unsafeMerge eid1 eid2 clss
      Control.pure (Ur True, clss)

{- | @'unsafeMerge' eid1 eid2 class@ merges the e-classes identified by @eid1@ and @eid2@, without cheking the exitence of the eids.
  Your must pass the canonical id as @eid1@, and the non-canonical id as @eid2@.

  Returns whether the meet differs from the leader's and subsumed class's
  former analysis values, respectively.
-}
{-# INLINEABLE unsafeMerge #-}
unsafeMerge ::
  forall α d l.
  ( Hashable1 l
  , Movable1 l
  , Analysis l d
  ) =>
  EClassId ->
  EClassId ->
  Mut α (EClasses d l) %1 ->
  BO α (Ur (Bool, Bool), Mut α (EClasses d l))
unsafeMerge eid1 eid2 clss
  | eid1 == eid2 = Control.pure (Ur (False, False), clss)
  | otherwise = Control.do
      (mr, clss) <- delete clss eid2
      let %1 !EClass {nodes = !rnodes, parentHistory = !rparentHistory, parentCount = !rparentCount, analysis = !ra} = case mr of
            Nothing -> error "EGraph.Types.EClasses.unsafeMerge: eid2 not found"
            Just eclass -> eclass
      let %1 !(Ur ranalysis) = move $ Ref.free ra
      let %1 !(Ur rparentsHistory) = move $ Ref.free rparentHistory
      let %1 !(Ur rparentsCount) = move $ Ref.free rparentCount
      reborrowing clss \clss0 -> Control.do
        let clss = coerceLin clss0 :: Mut _ (Raw d l)
        l <- HMB.lookup eid1 clss
        case l of
          Nothing -> error ("EClasses.unsafeMerge: canonical id not found: " <> show eid1) rnodes
          Just l -> Control.do
            let %1 !(Ur rnodes') = Ref.free rnodes
            l <- reborrowing_ l \l -> Control.do
              (Ur (), nodes) <-
                Ref.update
                  ( \(Ur lnodes) ->
                      Control.pure (Ur (), Ur (PHS.union lnodes rnodes'))
                  )
                  (l .# #nodes)
              Control.pure (consume nodes)
            l <- reborrowing_ l \l -> Control.do
              history <- Ref.modify (rparentsHistory <>) (l .# #parentHistory)
              Control.pure (consume history)
            l <- reborrowing_ l \l -> Control.do
              (Ur (), count) <-
                Ref.update
                  ( \count ->
                      move count & \(Ur count) ->
                        Control.pure (Ur (), rparentsCount P.+ count)
                  )
                  (l .# #parentCount)
              Control.pure (consume count)

            (changes, l) <- reborrowing l \l -> Control.do
              (changes, ref) <-
                Ref.update
                  ( \la ->
                      move la & \(Ur la) ->
                        let !new = la /\ ranalysis
                         in Control.pure (Ur (new P./= la, new P./= ranalysis), new)
                  )
                  (l .# #analysis)
              Control.pure $ ref `lseq` changes
            Control.pure $ l `lseq` changes

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear \ !a -> coerce a

{-# INLINEABLE size #-}
size :: Borrow k α (EClasses d l) %m -> BO α (Ur Int)
size = HMB.size . coerceLin
