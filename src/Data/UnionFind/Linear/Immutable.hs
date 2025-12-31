{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}

module Data.UnionFind.Linear.Immutable (
  UnionFind,
  freeze,
  thaw,
  find,

  -- * Unsafe operations
  unsafeThaw,
) where

import Data.Function ((&))
import Data.Ref.Linear (freeRef)
import Data.UnionFind.Linear (Key)
import Data.UnionFind.Linear qualified as Unborrowed
import Data.UnionFind.Linear.Borrowed qualified as Raw
import Data.UnionFind.Linear.Borrowed.Internal qualified as Raw
import GHC.Base (Multiplicity (..))
import Prelude.Linear (Ur (..), dup)
import Unsafe.Linear qualified as Unsafe

data UnionFind where
  UnionFind :: {-# UNPACK #-} !Raw.UnionFind %'Many -> UnionFind

-- | _O(1)_ converts a mutable UnionFind into an immutable one.
freeze :: Raw.UnionFind %1 -> Ur UnionFind
{-# NOINLINE freeze #-}
freeze = Unsafe.toLinear \ !uf -> Ur (UnionFind uf)

-- | _O(n)_ converts an immutable UnionFind into a mutable one.
thaw :: Ur UnionFind %1 -> Raw.UnionFind
{-# NOINLINE thaw #-}
thaw (Ur (UnionFind uf)) =
  dup uf & Unsafe.toLinear \(_, uf') -> uf'

{- | _O(1)_  __Unsafely__ conversts an immutable UnionFind into a mutable one.
This is unsafe because the resulting mutable UnionFind must not be used
after the immutable one is used.
-}
unsafeThaw :: UnionFind %1 -> Raw.UnionFind
{-# NOINLINE unsafeThaw #-}
unsafeThaw (UnionFind uf) = uf

find :: Key -> UnionFind -> Maybe Key
{-# INLINE find #-}
find key (UnionFind (Raw.UF uf)) =
  Unborrowed.find key (freeRef uf) & \(Ur mroot, _) -> mroot
