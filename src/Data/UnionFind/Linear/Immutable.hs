{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.UnionFind.Linear.Immutable (
  UnionFind (),
  Key (..),
  freeze,
  thaw,
  find,

  -- * Unsafe operations
  unsafeThaw,
) where

import Control.Monad.Borrow.Pure (Linearly)
import Control.Monad.Borrow.Pure.Freeze hiding (freeze, thaw, unsafeThaw)
import Control.Monad.Borrow.Pure.Freeze qualified as Freeze
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.UnionFind.Linear (Key)
import Data.UnionFind.Linear qualified as Unborrowed
import Data.UnionFind.Linear.Borrowed.Internal qualified as Raw
import GHC.Base (Multiplicity (..))
import GHC.Exts qualified as GHC
import Prelude.Linear (Ur (..), unur)
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe

{- | An immutable union-find structure, that supports 'find' operations only.
This can be converted to/from a mutable union-find structure using 'thaw' and 'freeze'.
-}
data UnionFind where
  UnionFind :: {-# UNPACK #-} !Unborrowed.UnionFind %'Many -> UnionFind

instance Freeze Raw.UnionFind UnionFind where
  basicFreeze = Unsafe.toLinear \(Raw.UF !uf) -> Ur $! UnionFind $! freeRef uf
  {-# NOINLINE basicUnsafeThaw #-}
  basicUnsafeThaw = GHC.noinline \(UnionFind !uf) lin ->
    Raw.UF PL.$! Ref.new uf lin

freeze :: Raw.UnionFind %1 -> Ur UnionFind
{-# INLINE freeze #-}
freeze = Freeze.freeze @Raw.UnionFind

thaw :: UnionFind -> Linearly %1 -> Raw.UnionFind
{-# INLINE thaw #-}
thaw = Freeze.thaw @UnionFind

unsafeThaw :: UnionFind -> Linearly %1 -> Raw.UnionFind
{-# INLINE unsafeThaw #-}
unsafeThaw = Freeze.unsafeThaw @UnionFind

{- | _O(1)_  __Unsafely__ conversts an immutable UnionFind into a mutable one.
This is unsafe because the resulting mutable UnionFind must not be used
after the immutable one is used.
-}
find :: Key -> UnionFind -> Maybe Key
{-# INLINE find #-}
find key (UnionFind !uf) =
  unur (fst $ Unborrowed.find key uf)
