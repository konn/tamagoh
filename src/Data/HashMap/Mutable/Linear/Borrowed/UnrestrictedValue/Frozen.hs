{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue.Frozen (
  -- * Construction
  freeze,
  thaw,

  -- * Query
  Keyed,
  lookup,
  size,

  -- * Iteration
  foldMapWithKey,

  -- * Unsafe operations
  unsafeThaw,
  unsafeFreeze,
) where

import Control.Lens (FoldableWithIndex)
import Control.Lens qualified as Lens
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Data.Array.Mutable.Linear qualified as Array
import Data.Function ((&))
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue (HashMapUr, Keyed)
import Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue.Internal qualified as Raw
import Data.HashMap.Mutable.Linear.Internal qualified as RawLin
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Prelude.Linear (Ur (..), dup)
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe
import Prelude hiding (lookup)

newtype ImmutableHashMapUr k v = ImmutableHashMapUr (RawLin.HashMap k v)

unsafeFreeze :: Share α (Raw.HashMapUr k v) %m -> Ur (ImmutableHashMapUr k v)
unsafeFreeze (UnsafeAlias (Raw.HM ref)) =
  Unsafe.toLinear Ur (ImmutableHashMapUr (freeRef ref))

freeze :: HashMapUr k v %1 -> Ur (ImmutableHashMapUr k v)
freeze (Raw.HM ref) = Unsafe.toLinear Ur (ImmutableHashMapUr (freeRef ref))

thaw :: ImmutableHashMapUr k v -> Linearly %1 -> HashMapUr k v
thaw (ImmutableHashMapUr hm) =
  dup hm PL.& \(!_, !hm') ->
    Raw.HM PL.. Ref.new hm'

unsafeThaw :: ImmutableHashMapUr k v -> Linearly %1 -> HashMapUr k v
unsafeThaw (ImmutableHashMapUr hm) = Raw.HM PL.. Ref.new hm

lookup :: (Keyed k) => k -> ImmutableHashMapUr k v -> Maybe v
lookup key (ImmutableHashMapUr hm) = RawLin.lookup key hm PL.& \(Ur !may, !_) -> may

size :: ImmutableHashMapUr k v -> Int
size (ImmutableHashMapUr hm) = RawLin.size hm & \(Ur !n, !_) -> n

foldMapWithKey :: (Monoid w) => (k -> v -> w) -> ImmutableHashMapUr k v -> w
foldMapWithKey f (ImmutableHashMapUr (RawLin.HashMap !_ !n !arr)) = go 0 mempty
  where
    go !i !acc
      | i >= n = acc
      | otherwise =
          case Array.unsafeGet i arr of
            (Ur Nothing, !_) -> go (i + 1) acc
            (Ur (Just (RawLin.RobinVal !_ !k !v)), !_) ->
              go (i + 1) (acc <> f k v)

instance Foldable (ImmutableHashMapUr k) where
  foldMap f (ImmutableHashMapUr (RawLin.HashMap !_ !n !arr)) = go 0 mempty
    where
      go !i !acc
        | i >= n = acc
        | otherwise =
            case Array.unsafeGet i arr of
              (Ur Nothing, !_) -> go (i + 1) acc
              (Ur (Just (RawLin.RobinVal !_ !_ !v)), !_) ->
                go (i + 1) (acc <> f v)

instance FoldableWithIndex k (ImmutableHashMapUr k) where
  ifoldMap = foldMapWithKey
  {-# INLINE ifoldMap #-}
