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
  new,
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
) where

import Control.Functor.Linear (void)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.ENode
import Data.Foldable (Foldable)
import Data.Functor.Classes (Show1)
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear
import Data.HashMap.Mutable.Linear.Borrowed (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.Hashable.Lifted (Hashable1)
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe.Linear
import Data.Set.Mutable.Linear.Borrowed (Set)
import Data.Set.Mutable.Linear.Borrowed qualified as Set
import Data.Traversable qualified as P
import Data.UnionFind.Linear.Borrowed (UnionFind)
import Data.UnionFind.Linear.Borrowed qualified as UF
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)
import GHC.Generics qualified as GHC
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear
import Prelude.Linear.Internal.Generically
import Text.Show.Borrowed (Display)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

newtype EClasses l = EClasses (Raw l)
  deriving newtype (Consumable)

type Raw l = HashMap EClassId (EClass l)

new :: Linearly %1 -> EClasses l
new = EClasses . HMB.empty 16

-- TODO: use (unsafe) indirection around Sets to reduce copying cost
data EClass l
  = EClass
  { nodes :: !(Set (ENode l))
  , parents :: !(HashMap (ENode l) EClassId)
  }
  deriving (GHC.Generic)

deriveGeneric ''EClass

deriving via Generically (EClass l) instance Consumable (EClass l)

deriving via Generically (EClass l) instance (Movable1 l) => Dupable (EClass l)

deriving via Generically (EClass l) instance (Copyable1 l, Show1 l) => Display (EClass l)

deriving via Raw l instance (Copyable1 l, Show1 l) => Display (EClasses l)

parents ::
  forall bk α l.
  (Movable1 l) =>
  Borrow bk α (EClasses l) %1 ->
  EClassId ->
  BO α (Ur [(ENode l, EClassId)])
parents clss0 eid = Control.do
  let %1 clss = coerceLin clss0 :: Borrow bk α (Raw l)
  mclass <- HMB.lookup eid clss
  case mclass of
    Nothing -> Control.pure (Ur [])
    Just eclass -> HMB.toList (eclass .# #parents)

delete ::
  forall α l.
  Mut α (EClasses l) %1 ->
  EClassId ->
  BO α (Maybe (EClass l), Mut α (EClasses l))
delete clss eid = Control.do
  let %1 !clss' = coerceLin clss :: Mut _ (Raw l)
  Bi.second coerceLin Control.<$> HMB.delete eid clss'

nodes ::
  forall bk α l.
  (Movable1 l) =>
  Borrow bk α (EClasses l) %1 ->
  EClassId ->
  BO α (Ur (Maybe (NonEmpty (ENode l))))
nodes clss0 eid = Control.do
  let %1 clss = coerceLin clss0 :: Borrow bk α (Raw l)
  mclass <- HMB.lookup eid clss
  case mclass of
    Nothing -> Control.pure (Ur Nothing)
    Just eclass -> Control.do
      Ur ns <- move Control.<$> Set.toList (eclass .# #nodes)
      Control.pure $ Ur (NonEmpty.nonEmpty ns)

setParents ::
  forall l α.
  (Hashable1 l) =>
  EClassId ->
  HashMap (ENode l) EClassId %1 ->
  Mut α (EClasses l) %1 ->
  BO α (Mut α (EClasses l))
setParents eid ps clss = Control.do
  reborrowing_ clss \clss0 -> Control.do
    let %1 !clss = coerceLin clss0 :: Mut _ (Raw l)
    mclass <- HMB.lookup eid clss
    case mclass of
      Nothing -> Control.pure $ consume ps
      Just eclass -> Control.do
        void $ HMB.swap ps (eclass .# #parents)

addParent ::
  (Hashable1 l) =>
  EClassId ->
  ENode l ->
  Mut α (EClass l) %1 ->
  BO α (Mut α (EClass l))
addParent pid enode eclass = Control.do
  eclass <- reborrowing_ eclass \eclass -> Control.do
    let %1 !parentsSet = eclass .# #parents
    void $ HMB.insert enode pid parentsSet
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
      nodes <- withLinearlyBO $ Control.pure . Set.singleton enode
      parents <- withLinearlyBO $ Control.pure . HMB.empty 16
      (mop, clss) <- HMB.insert eid EClass {parents, nodes} $ coerceLin clss
      clss <- reborrowing_ clss \clss -> Control.do
        chss <-
          mapMaybe (\(Ur _, e) -> e)
            Control.<$> HMB.lookups (children enode) clss
        void $ Data.forM chss \ch -> addParent eid enode ch
      mop `lseq` Control.pure (Ur True, coerceLin clss)

-- | Returns 'False' if the classes were already merged and no change will be made.
merge ::
  (Hashable1 l, Data.Functor l, Movable1 l, DistributesAlias l) =>
  EClassId ->
  EClassId ->
  Share α UnionFind ->
  Mut α (EClasses l) %1 ->
  BO α (Ur Bool, Mut α (EClasses l))
merge eid1 eid2 uf clss = Control.do
  (Ur mem1, clss) <- sharing clss $ \clss -> member eid1 clss
  (Ur mem2, clss) <- sharing clss $ \clss -> member eid2 clss
  if not mem1 || not mem2
    then Control.pure (Ur False, clss)
    else (Ur True,) Control.<$> unsafeMerge eid1 eid2 uf clss

unsafeMerge ::
  forall α l.
  (Hashable1 l, Movable1 l, Data.Functor l, DistributesAlias l) =>
  EClassId ->
  EClassId ->
  Share α UnionFind ->
  Mut α (EClasses l) %1 ->
  BO α (Mut α (EClasses l))
unsafeMerge eid1 eid2 uf clss
  | eid1 == eid2 = Control.pure clss
  | otherwise = Control.do
      Ur (EClassId -> canonId) <- UF.unsafeFind (coerce eid1) uf
      (Ur eid1, Ur eid2) <-
        if canonId == eid1
          then Control.pure (Ur eid1, Ur eid2)
          else Control.pure (Ur eid2, Ur eid1)
      (mr, clss) <- delete clss eid2
      let %1 !EClass {nodes = !rnodes, parents = !rparents} = case mr of
            Nothing -> error "EGraph.Types.EClasses.unsafeMerge: eid2 not found"
            Just eclass -> eclass
      clss <- reborrowing_ clss \clss0 -> Control.do
        let clss = coerceLin clss0 :: Mut _ (Raw l)
        l <- HMB.lookup eid1 clss
        case l of
          Nothing -> Control.pure $ rnodes `lseq` rparents `lseq` ()
          Just l -> Control.do
            (lnodes, l) <- reborrowing l \l -> Set.take_ (l .# #nodes)
            let %1 !nodes = Set.union lnodes rnodes

            (lparents, l) <- reborrowing l \l -> HMB.take_ (l .# #parents)
            let %1 !parents = HMB.union lparents rparents

            l <- reborrowing_ l \l -> Control.do
              void $ Set.swap nodes (l .# #nodes)
            Control.void $ reborrowing_ l \l -> Control.do
              void $ HMB.swap parents $ l .# #parents

      Control.pure clss

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear \ !a -> coerce a
