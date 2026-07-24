{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

{- | A borrowable, growable slot table addressed by dense 'Int' ids —
direct indexing instead of hashing (egglog-style class storage). The
borrow\/ownership discipline is identical to
"Data.HashMap.Mutable.Linear.Borrowed": lookups yield interior 'Borrow's
of the stored (linear) values, 'delete'\/'insert' return the displaced
value owned, and growth is transparent to outstanding borrows thanks to
the internal 'Data.Ref.Linear.Borrow.Ref' indirection.

Dense-id contract: capacity is proportional to the largest id ever
inserted (ids are expected to come from a dense allocator such as
@Data.UnionFind.Linear.fresh@ and never be reused).
-}
module Data.SlotMap.Mutable.Linear.Borrowed (
  SlotMap,
  empty,
  insert,
  delete,
  lookup,
  lookupsAll,
  member,
  size,
  toBorrowList,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.BO.Unsafe
import Control.Monad.Borrow.Pure.Utils (unsafeLeak)
import Data.Functor.Linear qualified as Data
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow qualified as Ref
import Data.SlotMap.Mutable.Linear.Borrowed.Internal
import Prelude.Linear hiding (insert, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

-- | An empty table with the given initial capacity.
empty :: Int -> Linearly %1 -> SlotMap v
empty cap l =
  dup l & \(l, l') -> SM $ Ref.new (rawEmptyL cap l) l'

{- | Store a value at the given id (amortized O(1); grows by doubling),
returning the slot's previous content owned.
-}
insert :: Int -> v %1 -> Mut α (SlotMap v) %1 -> BO α (Maybe v, Mut α (SlotMap v))
insert !i !v !sm = Control.do
  (mold, sm) <-
    Ref.update (\raw -> Control.pure (rawInsert i v raw)) (coerceBor sm)
  Control.pure (mold, recoerceBor sm)

-- | Clear the given id's slot, returning its content owned.
delete :: Int -> Mut α (SlotMap v) %1 -> BO α (Maybe v, Mut α (SlotMap v))
delete !i sm = Control.do
  (mold, sm) <-
    Ref.update (Control.pure . rawDelete i) (coerceBor sm)
  Control.pure (mold, recoerceBor sm)

askRaw ::
  (RawSlotMap v %1 -> (a, RawSlotMap v)) %1 ->
  Borrow bk α (SlotMap v) %m ->
  BO α a
askRaw f dic = case share dic of
  Ur !dic -> Control.do
    Ur (UnsafeAlias !raw) <- Ref.readShare (coerceBor dic)
    case f raw of
      -- NOTE: this @raw@ is a RAW memory block, so we MUST NOT 'consume' it
      -- here; intentionally leak the alias — the Lender eventually frees the
      -- whole block (same note as the borrowed hashmap).
      (!res, !raw) -> unsafeLeak raw `lseq` Control.pure res

-- | Number of live (present) entries.
size :: Borrow bk α (SlotMap v) %m -> BO α (Ur Int)
size = askRaw rawSize

member :: Int -> Borrow bk α (SlotMap v) %m -> BO α (Ur Bool)
member !i = askRaw (rawMember i)

-- | Borrow the value stored at the given id, if present.
lookup ::
  Int ->
  Borrow bk α (SlotMap v) %m ->
  BO α (Maybe (Borrow bk α v))
lookup !i !sm =
  Data.fmap UnsafeAlias . unur Control.<$> askRaw (rawLookup i) sm

-- | Look up every id in input order, including duplicates.
lookupsAll ::
  [Int] ->
  Borrow bk α (SlotMap v) %m ->
  BO α [(Ur Int, Maybe (Borrow bk α v))]
lookupsAll keys0 = Unsafe.toLinear \ !sm ->
  Data.forM (P.map Ur keys0) (\(Ur !k) -> lookup k sm Control.<&> \ !v -> (Ur k, v))
