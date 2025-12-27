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
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.Types.EClasses (
  EClasses (),
  lookup,
  parents,
  addParent,
  member,
  insertIfNew,
  merge,
  unsafeMerge,
) where

import Control.Functor.Linear (void)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Orphans (Movable1)
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.ENode
import Data.Foldable (Foldable)
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear
import Data.HashMap.Mutable.Linear.Borrowed (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.Hashable.Lifted (Hashable1)
import Data.Set.Mutable.Linear.Borrowed (Set)
import Data.Set.Mutable.Linear.Borrowed qualified as Set
import GHC.Generics qualified as GHC
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear
import Prelude.Linear.Internal.Generically
import Unsafe.Linear qualified as Unsafe

newtype EClasses l = EClasses (Raw l)

type Raw l = HashMap EClassId (EClass l)

-- TODO: use (unsafe) indirection around Sets to reduce copying cost
data EClass l
  = EClass
  { nodes :: !(Set (ENode l))
  , parents :: !(Set EClassId)
  }
  deriving (GHC.Generic)

deriveGeneric ''EClass

deriving via Generically (EClass l) instance Consumable (EClass l)

parents ::
  forall bk α l.
  EClassId -> Borrow bk α (EClasses l) %1 -> BO α (Ur (Maybe [EClassId]))
parents eid clss0 = Control.do
  let %1 clss = coerceLin clss0 :: Borrow bk α (Raw l)
  mclass <- HMB.lookup eid clss
  case mclass of
    Nothing -> Control.pure (Ur Nothing)
    Just eclass -> move . Just Control.<$> Set.toList (eclass .# #parents)

addParent ::
  EClassId ->
  Mut α (EClass l) %1 ->
  BO α (Mut α (EClass l))
addParent pid eclass = Control.do
  eclass <- reborrowing_ eclass \eclass -> Control.do
    let %1 !parentsSet = eclass .# #parents
    parentsSet <- Set.insert pid parentsSet
    Control.pure $ consume parentsSet
  Control.pure eclass

member ::
  forall l α.
  EClassId ->
  Share α (EClasses l) %1 ->
  BO α (Ur Bool)
member eid clss0 = Control.do
  let clss = coerceLin clss0 :: Share _ (Raw l)
  HMB.member eid clss

{- |
Returns 'True' if the node was newly inserted;
otherwise no change will be made and returns 'False'.
-}
insertIfNew ::
  forall l α.
  (Hashable1 l, Foldable l) =>
  EClassId ->
  ENode l ->
  Mut α (EClasses l) %1 ->
  BO α (Ur Bool, Mut α (EClasses l))
insertIfNew eid enode clss = Control.do
  (Ur mem, clss) <- sharing clss \clss -> member eid clss
  if mem
    then Control.pure (Ur False, coerceLin clss)
    else Control.do
      nodes <- Set.singleton enode
      parents <- Set.fromList $ children enode
      (mop, clss) <- HMB.insert eid EClass {parents, nodes} $ coerceLin clss
      () <- case mop of
        Nothing -> Control.pure ()
        Just x -> error "Cannot happen" x
      Control.pure (Ur True, coerceLin clss)

-- | Returns 'False' if the classes were already merged and no change will be made.
merge ::
  (Hashable1 l, Data.Functor l, Movable1 l, DistributesAlias l) =>
  EClassId ->
  EClassId ->
  Mut α (EClasses l) %1 ->
  BO α (Ur Bool, Mut α (EClasses l))
merge eid1 eid2 clss = Control.do
  (Ur mem1, clss) <- sharing clss $ \clss -> member eid1 clss
  (Ur mem2, clss) <- sharing clss $ \clss -> member eid2 clss
  if not mem1 || not mem2
    then Control.pure (Ur False, clss)
    else (Ur True,) Control.<$> unsafeMerge eid1 eid2 clss

unsafeMerge ::
  forall α l.
  (Hashable1 l, Movable1 l, Data.Functor l, DistributesAlias l) =>
  EClassId ->
  EClassId ->
  Mut α (EClasses l) %1 ->
  BO α (Mut α (EClasses l))
unsafeMerge eid1 eid2 clss = Control.do
  clss <- reborrowing_ clss \clss0 -> Control.do
    let clss = coerceLin clss0 :: Mut _ (Raw l)
    comps <- HMB.lookups [eid1, eid2] clss
    case comps of
      [(Ur _, set)] -> Control.pure $ consume set
      [(Ur _, Just l), (Ur _, Just r)] -> Control.do
        ((lnodes, lparents), l) <- sharing l \l ->
          (,)
            Control.<$> Set.toList (l .# #nodes)
            Control.<*> Set.toList (l .# #parents)
        ((rnodes, rparents), r) <- sharing r \r ->
          (,)
            Control.<$> Set.toList (r .# #nodes)
            Control.<*> Set.toList (r .# #parents)

        l <- reborrowing_ l \l -> Control.do
          void $ Set.inserts rnodes (l .# #nodes)
        Control.void $ reborrowing_ l \l -> Control.do
          void $ Set.inserts rparents $ l .# #parents

        r <- reborrowing_ r \r -> Control.do
          void $ Set.inserts lnodes (r .# #nodes)
        Control.void $ reborrowing_ r \r -> Control.do
          void $ Set.inserts lparents $ r .# #parents
      comps -> error "Cannot happen" comps

  Control.pure clss

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear coerce
