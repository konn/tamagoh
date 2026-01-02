{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.HashMap.Mutable.Linear.Borrowed (
  HashMap,
  Keyed,
  empty,
  fromList,
  insert,
  delete,
  alter,
  alterF,
  size,
  lookup,
  lookups,
  member,
  toList,
  toBorrowList,
  swap,
  take,
  take_,
  union,
) where

import Control.Functor.Linear (StateT (..), runStateT)
import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Monad.Borrow.Pure.Utils (deepCloneArray', swapTuple, unsafeLeak)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear qualified as Array
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (coerce)
import Data.Function qualified as P
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear (Keyed)
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Borrowed.Internal
import Data.HashMap.Mutable.Linear.Internal qualified as Raw
import Data.HashMap.Mutable.Linear.Witness qualified as Raw
import Data.HashSet qualified as IHS
import Data.Linear.Witness.Compat (fromPB)
import Data.Maybe qualified as P
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, take)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

inner :: HashMap k v %1 -> Ref (Raw.HashMap k v)
inner = Unsafe.toLinear \ !a -> coerce a

empty :: forall k v. (Keyed k) => Int -> Linearly %1 -> HashMap k v
empty size l =
  dup l & \(l, l'') -> HM $ Ref.new (Raw.emptyL size $ fromPB l) l''

fromList :: (Keyed k) => [(k, v)] %1 -> Linearly %1 -> HashMap k v
fromList = Unsafe.toLinear \ !keys -> \l ->
  dup l & \(l, l') ->
    HM $! Ref.new (Raw.fromListL keys $ fromPB l) l'

insert ::
  (Keyed k) =>
  k ->
  v %1 ->
  Mut α (HashMap k v) %1 ->
  BO α (Maybe v, Mut α (HashMap k v))
insert key !v !dic = Control.do
  (mval, dic) <-
    updateRef
      ( \dic ->
          Control.fmap swapTuple $
            flip runStateT (Just v) $
              Raw.alterF (\may -> StateT \ !s -> Control.pure (Unsafe.toLinear Ur s, may)) key dic
      )
      (coerceBor dic)
  Control.pure (mval, recoerceBor dic)

delete ::
  (Keyed k) => k -> Mut α (HashMap k v) %1 -> BO α (Maybe v, Mut α (HashMap k v))
delete key dic = Control.do
  (mval, dic) <-
    updateRef
      ( \dic ->
          Control.fmap swapTuple $
            flip runStateT Nothing $
              Raw.alterF (\may -> StateT \s -> Control.pure (Unsafe.toLinear Ur s, may)) key dic
      )
      (coerceBor dic)
  Control.pure (mval, recoerceBor dic)

forceMay :: Maybe a %1 -> Maybe a
forceMay = \case
  Nothing -> Nothing
  Just !x -> Just x

alter ::
  (Keyed k) =>
  (Maybe v %1 -> Maybe v) ->
  k ->
  Mut α (HashMap k v) %1 ->
  BO α (Mut α (HashMap k v))
alter f k =
  Control.fmap recoerceBor
    . modifyRef (Raw.alter (Unsafe.toLinear $ forceMay . f . forceMay) k)
    . coerceBor

alterF ::
  (Keyed k) =>
  (Maybe v %1 -> BO α (Maybe v)) ->
  k ->
  Mut α (HashMap k v) %1 ->
  BO α (Mut α (HashMap k v))
alterF f key dic = Control.do
  ((), dic) <-
    updateRef
      ( Control.fmap ((),)
          . Raw.alterF (Control.fmap (Unsafe.toLinear Ur . forceMay) . Unsafe.toLinear f . forceMay) key
      )
      (coerceBor dic)
  Control.pure $ recoerceBor dic

askRaw ::
  (Raw.HashMap k v %1 -> (a, Raw.HashMap k v)) %1 ->
  Borrow bk α (HashMap k v) %1 ->
  BO α a
askRaw f dic = case share dic of
  Ur !dic -> Control.do
    Ur (UnsafeAlias !dic) <- readSharedRef (coerceBor dic)
    case f dic of
      -- NOTE: This @dic@ is RAW memory block,
      -- so we MUST NOT 'consume' it here, and instead just intentionally leak it.
      -- This leakage won't cause memory leak, because Lender will eventually free the whole block.
      (!res, !dic) -> unsafeLeak dic `lseq` Control.pure res

size :: Borrow bk α (HashMap k v) %1 -> BO α (Ur Int)
size = askRaw Raw.size

lookup ::
  (Keyed k) =>
  k ->
  Borrow bk α (HashMap k v) %1 ->
  BO α (Maybe (Borrow bk α v))
lookup !key !dic =
  Data.fmap UnsafeAlias . unur Control.<$> askRaw (Raw.lookup key) dic

lookups ::
  (Keyed k) =>
  [k] ->
  Borrow bk α (HashMap k v) %1 ->
  BO α [(Ur k, (Maybe (Borrow bk α v)))]
lookups keys0 = Unsafe.toLinear \ !dic -> Control.do
  let keys = P.map Ur $ IHS.toList $ IHS.fromList keys0
  Data.forM keys (\(Ur !key) -> lookup key dic Control.<&> \ !v -> (Ur key, v))

member :: (Keyed k) => k -> Borrow bk α (HashMap k v) %1 -> BO α (Ur Bool)
member key = askRaw (Raw.member key)

askRaw_ ::
  (Movable a) =>
  (Raw.HashMap k v %1 -> a) %1 ->
  Borrow bk α (HashMap k v) %1 ->
  BO α a
{-# INLINE askRaw_ #-}
askRaw_ f dic = case share dic of
  Ur !dic -> Control.do
    Ur (UnsafeAlias !dic) <- readSharedRef (coerceBor dic)
    case move (f dic) of
      Ur !res -> Control.pure res

toList ::
  (Movable v) =>
  Borrow bk α (HashMap k v) %1 -> BO α (Ur [(k, v)])
toList =
  askRaw_ \(Raw.HashMap _ _ !robinArr) ->
    deepCloneArray' dupRobinVal robinArr & Unsafe.toLinear \(_, !robinArr) ->
      Array.toList robinArr
        & \(Ur elems) ->
          elems
            P.& P.catMaybes
            P.& P.map (\(Raw.RobinVal _ !k !v) -> (k, v))
            P.& Ur

swap ::
  forall k v α.
  HashMap k v %1 ->
  Mut α (HashMap k v) %1 ->
  BO α (HashMap k v, Mut α (HashMap k v))
swap keys dic = withLinearlyBO \lin -> Control.do
  Bi.second recoerceBor
    Control.<$> updateRef (\ !old -> Control.pure (HM $ Ref.new old lin, freeRef $ inner keys)) (coerceBor dic)

-- | Takes all elements from the set, leaving it empty.
take :: forall k v α. (Keyed k) => Mut α (HashMap k v) %1 -> BO α (HashMap k v, Mut α (HashMap k v))
take dic = Control.do
  Bi.second recoerceBor Control.<$> updateRef go (coerceBor dic)
  where
    go :: Raw.HashMap k v %1 -> BO α (HashMap k v, Raw.HashMap k v)
    go s = withLinearlyBO \lin ->
      dup lin & \(lin, lin') -> Control.do
        Control.pure (HM $! Ref.new s lin, Raw.emptyL 16 $! fromPB lin')

take_ :: forall k v α. (Keyed k) => Mut α (HashMap k v) %1 -> BO α (HashMap k v)
{-# INLINE take_ #-}
take_ set = Control.fmap (uncurry $ flip lseq) $ take set

union :: (Keyed k) => HashMap k v %1 -> HashMap k v %1 -> HashMap k v
union (HM ref1) (HM ref2) = DataFlow.do
  (l, ref1) <- withLinearly ref1
  HM $! Ref.new (Raw.union (freeRef ref1) (freeRef ref2)) l
