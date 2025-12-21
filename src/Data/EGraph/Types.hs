{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Types (
  EGraph,
  new,
  borrowNew,
  find,
  lookup,
  unsafeFind,
  canonicalize,
) where

import Control.Functor.Linear (asks, runReader)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.Coerce (Coercible, coerce)
import Data.Functor.Classes (Eq1, Ord1, Show1, compare1, eq1, showsPrec1)
import Data.Functor.Linear qualified as Data
import Data.HasField.Linear
import Data.HashMap.Mutable.Linear (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.HashMap.Mutable.Linear.Witness qualified as HMW
import Data.Hashable (Hashable (..))
import Data.Hashable.Lifted (Hashable1, hashWithSalt1)
import Data.Linear.Witness.Compat (fromPB)
import Data.Set.Mutable.Linear
import Data.UnionFind.Linear (Key, UnionFind)
import Data.UnionFind.Linear qualified as UF
import Data.UnionFind.Linear.Borrowed qualified as UFB
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear qualified as Ur
import GHC.Generics (Generic)
import Prelude.Linear hiding (Eq, Ord, Show, find, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude (Eq (..), Ord, Show)
import Prelude qualified as P

newtype EClassId = EClassId {getEClassId :: Key}
  deriving (Eq, Ord, Generic)
  deriving newtype (Show, Hashable, Consumable, Dupable, Movable)

newtype ENode f = ENode {app :: f EClassId}
  deriving (Generic)

instance (Hashable1 f) => Hashable (ENode f) where
  hashWithSalt = coerce P.$ hashWithSalt1 @f @EClassId
  {-# INLINE hashWithSalt #-}

instance (Show1 f) => Show (ENode f) where
  showsPrec = coerce P.$ showsPrec1 @f @EClassId
  {-# INLINE showsPrec #-}

instance (Eq1 f) => Eq (ENode f) where
  (==) = coerce P.$ eq1 @f @EClassId
  {-# INLINE (==) #-}

instance (Ord1 f) => Ord (ENode f) where
  compare = coerce P.$ compare1 @f @EClassId
  {-# INLINE compare #-}

data EGraph f = EGraph
  { unionFind :: !UnionFind
  , classes :: !(HashMap EClassId (Set (ENode f)))
  , hashcons :: !(HashMap (ENode f) EClassId)
  }
  deriving (Generic)

instance LinearOnly (EGraph f) where
  linearOnly :: LinearOnlyWitness (EGraph f)
  linearOnly = UnsafeLinearOnly

new :: (Hashable1 f) => Word -> Linearly %1 -> EGraph f
new capacity = runReader Control.do
  unionFind <- asks $ UF.newL capacity
  classes <- asks $ HMW.emptyL (P.fromIntegral capacity) . fromPB
  hashcons <- asks $ HMW.emptyL (P.fromIntegral capacity) . fromPB
  Control.pure EGraph {..}

borrowNew ::
  (Hashable1 f) =>
  Word ->
  Linearly %1 ->
  (Mut α (EGraph f), Lend α (EGraph f))
borrowNew capacity = borrowLinearOnly . new capacity

find :: Borrow k α (EGraph f) %1 -> EClassId -> BO α (Maybe (Ur EClassId))
find egraph (EClassId k) = Control.do
  let uf = egraph .# #unionFind
  coerceLin Data.<$> UFB.find k uf

lookup :: (P.Traversable l, Hashable1 l) => Share α (EGraph l) %1 -> ENode l -> BO α (Ur (Maybe EClassId))
lookup egraph enode =
  move egraph & \(Ur egraph) -> runUrT $ runMaybeT do
    enode <- MaybeT $ UrT (canonicalize egraph enode)
    MaybeT $ UrT $ HMB.lookup enode (egraph .# #hashcons)

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
