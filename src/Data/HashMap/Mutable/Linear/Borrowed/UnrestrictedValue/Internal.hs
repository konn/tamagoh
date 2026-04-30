{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
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
module Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue.Internal (
  module Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue.Internal,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.BO.Unsafe
import Control.Monad.Borrow.Pure.Utils
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Function qualified as P
import Data.HashMap.RobinHood.Mutable.Linear qualified as Raw
import Data.List qualified as P
import Data.Ref.Linear qualified as Ref
import Data.Ref.Linear.Borrow (Ref)
import Data.Ref.Linear.Borrow qualified as Ref
import GHC.TypeError (Unsatisfiable, unsatisfiable)
import GHC.TypeLits (ErrorMessage (..))
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, take)
import Text.Show.Borrowed (Display (..))
import Unsafe.Linear qualified as Unsafe

{- | A mutable HashMap with unrestricted keys and values.
The constructor is not exported to maintain invariants.
-}
newtype HashMapUr k v = HM (Ref (Raw.HashMap k v))
  deriving newtype (LinearOnly)

instance Consumable (HashMapUr k v) where
  consume = \(HM ref) -> consume $ Ref.free ref
  {-# INLINE consume #-}

-- | Dupable instance without deep cloning (values are unrestricted).
instance Dupable (HashMapUr k v) where
  {-# NOINLINE dup2 #-}
  dup2 = Unsafe.toLinear \(HM !ref) -> DataFlow.do
    (lin, !ref) <- withLinearly ref
    (ref, !hm) <- Unsafe.toLinear (\ref -> (ref, Ref.free ref)) ref
    !hm' <- Unsafe.toLinear (\(!_, !hm') -> hm') $ dup hm
    (HM ref, HM $! Ref.new hm' lin)

-- | 'HashMapUr' _CANNOT_ be 'Copyable', because it contains a mutable reference.
instance
  (Unsatisfiable ('ShowType (HashMapUr k v) ':<>: 'Text " cannot be Copyable")) =>
  Copyable (HashMapUr k v)
  where
  copy = unsatisfiable

-- | Copyable instance without deep cloning (values are unrestricted).
instance Clone (HashMapUr k v) where
  clone = Unsafe.toLinear \(UnsafeAlias (HM !ref)) -> Control.do
    lin <- askLinearly
    !hm <- Control.pure (Ref.free ref)
    !hm' <- Unsafe.toLinear (\(!_, !hm') -> Control.pure hm') $ dup hm
    Control.pure $ HM $! Ref.new hm' lin

instance (Show k, Show v) => Display (HashMapUr k v) where
  displayPrec _ bor = Control.do
    Ur lst <- toList bor
    Control.pure $
      Ur $
        showString "{"
          P.. P.foldr
            (P..)
            id
            ( P.intersperse
                (showString ", ")
                [showChar '(' P.. showsPrec 0 k P.. showString ", " P.. showsPrec 0 v P.. showChar ')' | (k, v) <- lst]
            )
          P.. showString "}"

askRaw_ ::
  (Raw.HashMap k v %1 -> a) %1 ->
  Borrow bk α (HashMapUr k v) %m ->
  BO α a
{-# INLINE askRaw_ #-}
askRaw_ f dic = case share dic of
  Ur !dic -> Control.do
    Ur (UnsafeAlias !dic) <- Ref.readShare (coerceBor dic)
    case f dic of
      !res -> Control.pure res

inner :: HashMapUr k v %1 -> Ref (Raw.HashMap k v)
inner = coerceLin

coerceBor ::
  forall k v bk α.
  Borrow bk α (HashMapUr k v) %1 ->
  Borrow bk α (Ref (Raw.HashMap k v))
{-# INLINE coerceBor #-}
coerceBor = coerceLin

recoerceBor ::
  forall k v bk α.
  Borrow bk α (Ref (Raw.HashMap k v)) %1 ->
  Borrow bk α (HashMapUr k v)
{-# INLINE recoerceBor #-}
recoerceBor = coerceLin

askRaw ::
  (Raw.HashMap k v %1 -> (a, Raw.HashMap k v)) %1 ->
  Borrow bk α (HashMapUr k v) %m ->
  BO α a
askRaw f dic = case share dic of
  Ur !dic -> Control.do
    Ur (UnsafeAlias !dic) <- Ref.readShare (coerceBor dic)
    case f dic of
      -- NOTE: This @dic@ is RAW memory block,
      -- so we MUST NOT 'consume' it here, and instead just intentionally leak it.
      -- This leakage won't cause memory leak, because Lender will eventually free the whole block.
      (!res, !dic) -> unsafeLeak dic `lseq` Control.pure res

{- | Convert the HashMap to a list. Uses tail-recursive implementation
with strict accumulator to avoid thunks.
-}
toList :: Borrow bk α (HashMapUr k v) %m -> BO α (Ur [(k, v)])
toList = askRaw_ rawToList'

-- Almost same as 'Raw.toList', but it uses DList and tail-recursion and forces
-- thunks to avoid mutation after read.
rawToList' :: Raw.HashMap k v %1 -> Ur [(k, v)]
{-# INLINE rawToList' #-}
rawToList' = Raw.toList
