{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.Types.EClasses (
  EClasses (),
  member,
  insertIfNew,
  merge,
  unsafeMerge,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Orphans ()
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.ENode
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear.Borrowed (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable.Lifted (Hashable1)
import Prelude.Linear
import Unsafe.Linear qualified as Unsafe

-- TODO: consider using mutable sets under the hood?
newtype EClasses l = EClasses (Raw l)

type Raw l = HashMap EClassId (HashSet (ENode l))

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
  (Hashable1 l) =>
  EClassId ->
  ENode l ->
  Mut α (EClasses l) %1 ->
  BO α (Ur Bool, Mut α (EClasses l))
insertIfNew eid enode clss = Control.do
  (Ur mem, clss) <- sharing_ clss \clss -> member eid clss
  if mem
    then Control.pure (Ur False, coerceLin clss)
    else Control.do
      (mop, clss) <- HMB.insert eid (HS.singleton enode) $ coerceLin clss
      () <- case mop of
        Nothing -> Control.pure ()
        Just x -> error "Cannot happen" x
      Control.pure (Ur True, coerceLin clss)

-- | Returns 'False' if the classes were already merged and no change will be made.
merge ::
  (Hashable1 l, Data.Functor l, DistributesAlias l) =>
  EClassId ->
  EClassId ->
  Mut α (EClasses l) %1 ->
  BO α (Ur Bool, Mut α (EClasses l))
merge eid1 eid2 clss = Control.do
  (Ur mem1, clss) <- sharing_ clss $ \clss -> member eid1 clss
  (Ur mem2, clss) <- sharing_ clss $ \clss -> member eid2 clss
  if not mem1 || not mem2
    then Control.pure (Ur False, clss)
    else (Ur True,) Control.<$> unsafeMerge eid1 eid2 clss

unsafeMerge ::
  forall α l.
  (Hashable1 l, Data.Functor l, DistributesAlias l) =>
  EClassId ->
  EClassId ->
  Mut α (EClasses l) %1 ->
  BO α (Mut α (EClasses l))
unsafeMerge eid1 eid2 clss0 = Control.do
  let clss = coerceLin clss0 :: Mut _ (Raw l)
  (mnew, clss) <- sharing_ clss \clss -> Control.do
    comps <- HMB.lookups [eid1, eid2] clss
    case comps of
      [(Ur _, set)] -> set `lseq` Control.pure Nothing
      [(Ur _, Just l), (Ur _, Just r)] -> Control.do
        Control.pure $ Just (copy l, copy r)
      comps -> error "Cannot happen" comps
  clss <- case mnew of
    Nothing -> Control.pure clss
    Just (l, r) -> Control.do
      clss <-
        HMB.alter
          ( \ml -> case ml of
              Nothing -> Just r
              Just l -> Just $ HS.union l r
          )
          eid1
          clss
      clss <-
        HMB.alter
          ( \mr -> case mr of
              Nothing -> Just l
              Just r -> Just (HS.union l r)
          )
          eid2
          clss
      Control.pure clss

  Control.pure $ coerceLin clss

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear coerce
