{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.Vector.Unboxed.Mutable.Growable.Borrowed (
  Vector,
  Unbox,
  new,
  fromList,
  size,
  push,
  pop,
  get,
  unsafeGet,
  set,
  null,
  unsafeSet,
  capacity,
  takeOut,
  takeOut_,
  toList,
  borrowToList,
  freeze,
) where

import Control.Functor.Linear (reader, runReader)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Monad.Borrow.Pure.Utils
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear.Unboxed (Unbox)
import Data.Bifunctor.Linear qualified as Bi
import Data.Functor.Linear qualified as Data
import Data.Linear.Witness.Compat
import Data.Ref.Linear qualified as Ref
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Prelude.Linear hiding (null)
import Text.Show.Borrowed
import Unsafe.Linear qualified as Unsafe

newtype Vector a = Vector (Ref (LUV.Vector a))

instance Consumable (Vector a) where
  consume (Vector ref) = consume ref

instance (Unbox a) => Dupable (Vector a) where
  dup2 = Unsafe.toLinear \(Vector !ref) -> DataFlow.do
    (lin, !ref) <- withLinearly ref
    (ref, !hm) <- Unsafe.toLinear (\ref -> (ref, Ref.freeRef ref)) ref
    !hm' <- Unsafe.toLinear (\(!_, !hm') -> hm') $ dup hm
    (Vector ref, Vector $! Ref.new hm' lin)

freeze :: (U.Unbox a) => Vector a %1 -> Ur (U.Vector a)
freeze (Vector ref) = LUV.freeze $ Ref.freeRef ref

new :: (Unbox a) => Linearly %1 -> Vector a
new l = flip runReader l Control.do
  !vec <- reader $ LUV.emptyL . fromPB
  Vector Control.<$> reader (Ref.new vec)

fromList :: (Unbox a) => [a] -> Linearly %1 -> Vector a
fromList xs l = flip runReader l Control.do
  !vec <- reader $ LUV.fromListL xs . fromPB
  Vector Control.<$> reader (Ref.new vec)

size :: Borrow bk α (Vector a) %m -> BO α (Ur Int)
{-# INLINE size #-}
size = askRaw LUV.size

capacity :: (Unbox a) => Borrow bk α (Vector a) %m -> BO α (Ur Int)
{-# INLINE capacity #-}
capacity = askRaw LUV.capacity

push :: (Unbox a) => a -> Mut α (Vector a) %1 -> BO α (Mut α (Vector a))
push !x vec = Control.do
  recoerceBor Control.<$> modifyRef (LUV.push x) (coerceBor vec)

null :: Borrow bk α (Vector a) %m -> BO α (Ur Bool)
null = Control.fmap (Data.fmap (== 0)) . size

pop :: (Unbox a) => Mut α (Vector a) %1 -> BO α (Ur (Maybe a), Mut α (Vector a))
pop vec = Control.do
  Bi.second recoerceBor
    Control.<$> updateRef
      (\vec -> Control.pure $! LUV.pop vec)
      (coerceBor vec)

recoerceBor :: Borrow bk α (Ref (LUV.Vector a)) %1 -> Borrow bk α (Vector a)
recoerceBor = coerceLin

askRaw ::
  (LUV.Vector a %1 -> (b, LUV.Vector a)) %1 ->
  Borrow bk α (Vector a) %m ->
  BO α b
{-# INLINE askRaw #-}
askRaw f !vec = case share vec of
  Ur !dic -> Control.do
    Ur (UnsafeAlias !dic) <- readSharedRef (coerceBor dic)
    case f dic of
      -- NOTE: This @dic@ is RAW memory block,
      -- so we MUST NOT 'consume' it here, and instead just intentionally leak it.
      -- This leakage won't cause memory leak, because Lender will eventually free the whole block.
      (!res, !dic) -> unsafeLeak dic `lseq` Control.pure res

get :: (Unbox a) => Int -> Borrow bk α (Vector a) %m -> BO α (Ur a)
{-# INLINE get #-}
get !i = askRaw $ LUV.get i

unsafeGet :: (Unbox a) => Int -> Borrow bk α (Vector a) %m -> BO α (Ur a)
{-# INLINE unsafeGet #-}
unsafeGet !i = askRaw $ LUV.unsafeGet i

set :: (Unbox a) => Int -> a -> Mut α (Vector a) %1 -> BO α (Mut α (Vector a))
{-# INLINE set #-}
set !i !x vec = Control.do
  recoerceBor Control.<$> modifyRef (LUV.set i x) (coerceBor vec)

unsafeSet :: (Unbox a) => Int -> a -> Mut α (Vector a) %1 -> BO α (Mut α (Vector a))
{-# INLINE unsafeSet #-}
unsafeSet !i !x vec = Control.do
  recoerceBor Control.<$> modifyRef (LUV.unsafeSet i x) (coerceBor vec)

coerceBor :: Borrow bk α (Vector a) %1 -> Borrow bk α (Ref (LUV.Vector a))
{-# INLINE coerceBor #-}
coerceBor = coerceLin

takeOut :: (Unbox a) => Mut α (Vector a) %1 -> BO α (Vector a, Mut α (Vector a))
takeOut vec = Control.do
  Bi.second recoerceBor
    Control.<$> updateRef
      ( \vec -> asksLinearlyM \lin ->
          dup lin & \(lin, lin') -> Control.pure (Vector $ Ref.new vec lin, LUV.emptyL $ fromPB lin')
      )
      (coerceBor vec)

takeOut_ :: (Unbox a) => Mut α (Vector a) %1 -> BO α (Vector a)
takeOut_ = Control.fmap (uncurry $ flip lseq) . takeOut

toList :: (Unbox a) => Vector a %1 -> Ur [a]
toList (Vector ref) = LUV.toList $ Ref.freeRef ref

borrowToList :: (Unbox a) => Borrow bk α (Vector a) %m -> BO α (Ur [a])
borrowToList = askRaw_ LUV.toList

instance (Unbox a, Show a) => Display (Vector a) where
  displayPrec _ bor = Control.do
    Ur lst <- borrowToList bor
    Control.pure $ Ur $ shows lst

askRaw_ ::
  (LUV.Vector a %1 -> x) %1 ->
  Borrow bk α (Vector a) %m ->
  BO α x
askRaw_ f dic = case share dic of
  Ur !dic -> Control.do
    Ur (UnsafeAlias !dic) <- readSharedRef (coerceBor dic)
    case f dic of
      !res -> Control.pure res
