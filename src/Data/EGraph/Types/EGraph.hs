{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
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
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Coerce (Coercible, coerce)
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.EClasses (EClasses)
import Data.EGraph.Types.EClasses qualified as EC
import Data.EGraph.Types.ENode
import Data.Functor.Classes (Eq1)
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear
import Data.HashMap.Mutable.Linear (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.Hashable.Lifted (Hashable1)
import Data.Maybe (isJust)
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

add :: (P.Traversable l, Hashable1 l) => ENode l -> Mut α (EGraph l) %1 -> BO α (Ur EClassId, Mut α (EGraph l))
add enode egraph = Control.do
  (Ur mid, egraph) <- sharing_ egraph \egraph ->
    lookup enode egraph
  case mid of
    Just eid -> Control.pure (Ur eid, egraph)
    Nothing -> Control.do
      (Ur eid, egraph) <- reborrowing_ egraph \egraph -> Control.do
        (eid, uf) <- UFB.fresh (egraph .# #unionFind)
        Control.pure $ uf `lseq` Ur.lift EClassId eid
      ((), egraph) <- reborrowing_ egraph \egraph -> Control.do
        let %1 !classes = egraph .# #classes
        (Ur _, classes) <- EC.insertIfNew eid enode classes
        Control.pure $ consume classes

      Control.pure (Ur eid, egraph)

merge ::
  ( Data.Functor l
  , DistributesAlias l
  , Hashable1 l
  ) =>
  EClassId -> EClassId -> Mut α (EGraph l) %1 -> BO α (Ur Bool, Mut α (EGraph l))
merge eid1 eid2 egraph = Control.do
  (Ur merged, egraph) <- reborrowing_ egraph \egraph -> Control.do
    let %1 !uf = egraph .# #unionFind
    (merged, uf) <- UFB.union eid1.getKey eid2.getKey uf
    Control.pure $ uf `lseq` Ur.lift isJust merged
  if merged
    then Control.do
      ((), egraph) <- reborrowing_ egraph \egraph -> Control.do
        let %1 !classes = egraph .# #classes
        classes <- EC.merge eid1 eid2 classes
        Control.pure $ consume classes
      Control.pure (Ur True, egraph)
    else Control.pure (Ur False, egraph)
