{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{- | Efficient union-find data structure with path compression,
using linear types for safe mutation and unboxed vectors for performance.

This module provides both unsafe (fast) and safe (bounds-checked) APIs.
The unsafe variants follow the same convention as vector libraries:
they are fast but can crash on invalid input. The safe variants
return Maybe values or Bool success indicators.

Elements are represented by 'Key' values which wrap Word indices.
-}
module Data.UnionFind.Linear.Internal (
  module Data.UnionFind.Linear.Internal,
) where

import Control.Monad.Borrow.Pure (Copyable)
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Data.Hashable (Hashable)
import Data.Ord.Linear qualified as Linear
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VGM
import Data.Vector.Mutable.Linear.Unboxed (Vector)
import Data.Vector.Unboxed qualified as U
import Prelude.Linear hiding (Eq (..), Num (..), Ord (..), find, (+), (-))
import Unsafe.Linear qualified as Unsafe
import Prelude (Eq (..), Num (..), Ord (..))

{- | A key representing an element in the union-find structure.
Keys are zero-indexed Word values.
-}
newtype Key = Key {getKey :: Word}
  deriving newtype
    ( Prelude.Eq
    , Prelude.Ord
    , Prelude.Num
    , Show
    , Enum
    , Integral
    , Real
    , Bounded
    , Hashable
    , Consumable
    , Dupable
    , Movable
    , Copyable
    , U.Unbox
    )

newtype instance U.MVector s Key = MV_Key (U.MVector s Word)

deriving newtype instance VGM.MVector U.MVector Key

deriving newtype instance VG.Vector U.Vector Key

newtype instance U.Vector Key = V_Key (U.Vector Word)

instance Linear.Eq Key where
  (==) = Unsafe.coerce $ (Prelude.==) @Word
  {-# INLINE (==) #-}

instance Linear.Ord Key where
  compare = Unsafe.coerce $ Prelude.compare @Word
  {-# INLINE compare #-}
  (<=) = Unsafe.coerce $ (Prelude.<=) @Word
  {-# INLINE (<=) #-}
  (<) = Unsafe.coerce $ (Prelude.<) @Word
  {-# INLINE (<) #-}
  (>=) = Unsafe.coerce $ (Prelude.>=) @Word
  {-# INLINE (>=) #-}
  (>) = Unsafe.coerce $ (Prelude.>) @Word
  {-# INLINE (>) #-}

{- | A union-find (disjoint-set) data structure specialized for 'Key' elements.
Elements are represented by indices 0..n-1.

The structure maintains two unboxed vectors:
* Parent pointers for the tree structure
* Ranks for the union-by-rank heuristic

All fields are strict to prevent space leaks.
-}
data UnionFind where
  UnionFind :: !Word -> !(Vector Key) %1 -> !(Vector Word) %1 -> UnionFind

instance Consumable UnionFind where
  -- TODO: stop leaking
  consume (UnionFind _ p r) = consume p `lseq` consume r

instance Dupable UnionFind where
  dup2 (UnionFind n p r) =
    let %1 !(p1, p2) = dup p
        %1 !(r1, r2) = dup r
     in (UnionFind n p1 r1, UnionFind n p2 r2)

instance LinearOnly UnionFind where
  linearOnly :: LinearOnlyWitness UnionFind
  linearOnly = UnsafeLinearOnly
