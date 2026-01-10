{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{- |
A borrowed HashMap with unrestricted (immutable) keys and values.

Unlike "Data.HashMap.Mutable.Linear.Borrowed", this variant does not
support linear/mutable values. Both keys and values must be unrestricted.
This allows for faster duplication (no deep cloning needed) and more
efficient iteration.
-}
module Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue (
  HashMapUr,
  Keyed,

  -- * Construction
  empty,
  fromList,

  -- * Mutation
  insert,
  delete,
  alter,
  alterF,

  -- * Query
  size,
  lookup,
  member,

  -- * Iteration
  toList,

  -- * Bulk operations
  swap,
  take,
  take_,
  union,
) where

import Control.Functor.Linear (StateT (..), runStateT)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Bifunctor.Linear qualified as Bi
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear (Keyed)
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue.Internal
import Data.HashMap.Mutable.Linear.Witness qualified as Raw
import Data.Linear.Witness.Compat (fromPB)
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, take)

-- * Construction

empty :: forall k v. (Keyed k) => Int -> Linearly %1 -> HashMapUr k v
empty size l =
  dup l & \(l, l'') -> HM $ Ref.new (Raw.emptyL size $ fromPB l) l''

fromList :: (Keyed k) => [(k, v)] -> Linearly %1 -> HashMapUr k v
fromList dic l =
  dup l & \(l, l') ->
    HM $! Ref.new (Raw.fromListL dic $ fromPB l) l'

-- * Mutation

insert ::
  (Keyed k) =>
  k ->
  v ->
  Mut α (HashMapUr k v) %1 ->
  BO α (Ur (Maybe v), Mut α (HashMapUr k v))
insert key !v !dic = Control.do
  (Ur mval, dic) <-
    updateRef
      ( \dic ->
          Control.fmap swapTuple $
            flip runStateT (Ur (Just v)) $
              Raw.alterF (\ !may -> StateT \ !s -> Control.pure (s, Ur may)) key dic
      )
      (coerceBor dic)
  Control.pure (Ur $ forceMay mval, recoerceBor dic)

delete ::
  (Keyed k) => k -> Mut α (HashMapUr k v) %1 -> BO α (Ur (Maybe v), Mut α (HashMapUr k v))
delete key dic = Control.do
  (Ur mval, dic) <-
    updateRef
      ( \dic ->
          Control.fmap swapTuple $
            flip runStateT (Ur Nothing) $
              Raw.alterF (\ !may -> StateT \ !s -> Control.pure (s, Ur may)) key dic
      )
      (coerceBor dic)
  Control.pure (Ur $ forceMay mval, recoerceBor dic)

swapTuple :: (a, b) %1 -> (b, a)
swapTuple (a, b) = (b, a)

forceMay :: Maybe a %1 -> Maybe a
forceMay = \case
  Nothing -> Nothing
  Just !x -> Just x

alter ::
  (Keyed k) =>
  (Maybe v -> Maybe v) ->
  k ->
  Mut α (HashMapUr k v) %1 ->
  BO α (Mut α (HashMapUr k v))
alter f k =
  Control.fmap recoerceBor
    . modifyRef (Raw.alter f k)
    . coerceBor

alterF ::
  (Keyed k) =>
  (Maybe v -> BO α (Ur (Maybe v))) ->
  k ->
  Mut α (HashMapUr k v) %1 ->
  BO α (Mut α (HashMapUr k v))
alterF f key dic = Control.do
  ((), dic) <-
    updateRef
      ( Control.fmap ((),)
          . Raw.alterF (\ !may -> Data.fmap forceMay Control.<$> f (forceMay may)) key
      )
      (coerceBor dic)
  Control.pure $ recoerceBor dic

-- * Query

size :: Borrow bk α (HashMapUr k v) %m -> BO α (Ur Int)
size = askRaw Raw.size

lookup ::
  (Keyed k) =>
  k ->
  Borrow bk α (HashMapUr k v) %m ->
  BO α (Ur (Maybe v))
lookup !key !dic = askRaw (Raw.lookup key) dic

member :: (Keyed k) => k -> Borrow bk α (HashMapUr k v) %m -> BO α (Ur Bool)
member key = askRaw (Raw.member key)

-- * Bulk operations

swap ::
  forall k v α.
  HashMapUr k v %1 ->
  Mut α (HashMapUr k v) %1 ->
  BO α (HashMapUr k v, Mut α (HashMapUr k v))
swap keys dic = asksLinearlyM \lin -> Control.do
  Bi.second recoerceBor
    Control.<$> updateRef (\ !old -> Control.pure (HM $ Ref.new old lin, freeRef $ inner keys)) (coerceBor dic)

-- | Takes all elements from the map, leaving it empty.
take :: forall k v α. (Keyed k) => Mut α (HashMapUr k v) %1 -> BO α (HashMapUr k v, Mut α (HashMapUr k v))
take dic = Control.do
  Bi.second recoerceBor Control.<$> updateRef go (coerceBor dic)
  where
    go :: Raw.HashMap k v %1 -> BO α (HashMapUr k v, Raw.HashMap k v)
    go s = asksLinearlyM \lin ->
      dup lin & \(lin, lin') -> Control.do
        Control.pure (HM $! Ref.new s lin, Raw.emptyL 16 $! fromPB lin')

take_ :: forall k v α. (Keyed k) => Mut α (HashMapUr k v) %1 -> BO α (HashMapUr k v)
{-# INLINE take_ #-}
take_ dic = Control.fmap (uncurry $ flip lseq) $ take dic

union :: (Keyed k) => HashMapUr k v %1 -> HashMapUr k v %1 -> HashMapUr k v
union (HM ref1) (HM ref2) = DataFlow.do
  (l, ref1) <- withLinearly ref1
  HM $! Ref.new (Raw.union (freeRef ref1) (freeRef ref2)) l
