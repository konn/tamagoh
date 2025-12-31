{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.Set.Mutable.Linear.Borrowed (
  Set,
  empty,
  singleton,
  fromList,
  insert,
  inserts,
  member,
  null,
  size,
  toList,
  toBorrowList,
  toListUnborrowed,
  take,
  take_,
  swap,
  union,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Control.Monad.Borrow.Pure.Utils (deepCloneArray', unsafeLeak)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear qualified as Array
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (Coercible, coerce)
import Data.Function qualified as P
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear.Borrowed.Internal (dupRobinVal)
import Data.HashMap.Mutable.Linear.Internal qualified as RawHM
import Data.Linear.Witness.Compat (fromPB)
import Data.Maybe qualified as P
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Data.Set.Mutable.Linear (Keyed)
import Data.Set.Mutable.Linear.Borrowed.Internal
import Data.Set.Mutable.Linear.Internal qualified as Raw
import Data.Set.Mutable.Linear.Witness qualified as Raw
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, null, take)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

inner :: Set k %1 -> Ref (Raw.Set k)
{-# INLINE inner #-}
inner = coerceLin

empty :: (Keyed k) => Int -> Linearly %1 -> Set k
empty size l =
  dup l & \(l, l') ->
    Set $ Ref.new (Raw.emptyL size $ fromPB l) l'

singleton :: (Keyed k) => k -> Linearly %1 -> Set k
singleton !key l =
  dup l & \(l, l') ->
    Set $! Ref.new (Raw.fromListL [key] $ fromPB l) l'

fromList :: (Keyed k) => [k] -> Linearly %1 -> Set k
fromList = Unsafe.toLinear \ !keys -> \l ->
  dup l & \(l, l') ->
    Set $! Ref.new (Raw.fromListL keys $ fromPB l) l'

insert :: (Keyed k) => k -> Mut α (Set k) %1 -> BO α (Mut α (Set k))
insert = Unsafe.toLinear \ !key -> \ !set -> Control.do
  set <- modifyRef (\ !s -> Raw.insert key s) (coerceBor set)
  Control.pure $! recoerceBor set

inserts :: (Keyed k) => [k] -> Mut α (Set k) %1 -> BO α (Mut α (Set k))
{-# INLINE inserts #-}
inserts [] old = Control.pure old
inserts (k : ks) old = Control.do
  old <- insert k old
  inserts ks old

askRaw ::
  (Raw.Set k %1 -> (a, Raw.Set k)) %1 ->
  Borrow bk α (Set k) %1 ->
  BO α a
askRaw f dic = case share dic of
  Ur dic -> Control.do
    Ur (UnsafeAlias dic) <- readSharedRef (coerceBor dic)
    case f dic of
      -- NOTE: This @dic@ is RAW memory block,
      -- so we MUST NOT 'consume' it here, and instead just intentionally leak it.
      -- This leakage won't cause memory leak, because Lender will eventually free the whole block.
      (!res, !dic) -> unsafeLeak dic `lseq` Control.pure res

member ::
  forall k α.
  (Keyed k) =>
  k ->
  Share α (Set k) %1 ->
  BO α (Ur Bool)
member key = askRaw (Raw.member key)

toList :: Borrow bk α (Set k) %1 -> BO α [k]
toList =
  askRaw_
    ( \(Raw.Set (RawHM.HashMap _ _ robinArr)) ->
        deepCloneArray' dupRobinVal robinArr & Unsafe.toLinear \(_, !robinArr) ->
          Array.toList robinArr
            & \(Ur elems) ->
              elems
                P.& P.catMaybes
                P.& P.map (\(RawHM.RobinVal _ !k ()) -> k)
    )

toListUnborrowed :: (Keyed k) => Set k %1 -> [k]
toListUnborrowed (Set ref) = unur $ Raw.toList (freeRef ref)

null :: (Keyed k) => Borrow bk α (Set k) %1 -> BO α (Ur Bool)
{-# INLINE null #-}
null set = askRaw (Bi.first (Data.fmap (== 0)) . Raw.size) set

size :: (Keyed k) => Borrow bk α (Set k) %1 -> BO α (Ur Int)
{-# INLINE size #-}
size = askRaw Raw.size

-- | Takes all elements from the set, leaving it empty.
take :: forall k α. (Keyed k) => Mut α (Set k) %1 -> BO α (Set k, Mut α (Set k))
take set = Control.do
  Bi.second recoerceBor Control.<$> updateRef go (coerceBor set)
  where
    go :: Raw.Set k %1 -> BO α (Set k, Raw.Set k)
    go s = withLinearlyBO \lin ->
      dup lin & \(lin, lin') -> Control.do
        Control.pure (Set $ Ref.new s lin, Raw.emptyL 16 $ fromPB lin')

take_ :: forall k α. (Keyed k) => Mut α (Set k) %1 -> BO α (Set k)
{-# INLINE take_ #-}
take_ = Control.fmap (uncurry $ flip lseq) . take

swap ::
  forall k α.
  Set k %1 ->
  Mut α (Set k) %1 ->
  BO α (Set k, Mut α (Set k))
swap keys dic = withLinearlyBO \lin -> Control.do
  Bi.second recoerceBor
    Control.<$> updateRef (\old -> Control.pure (Set $! Ref.new old lin, freeRef $ inner keys)) (coerceBor dic)

coerceLin :: (Coercible a b) => a %1 -> b
coerceLin = Unsafe.toLinear \ !a -> coerce a

union :: (Keyed k) => Set k %1 -> Set k %1 -> Set k
union (Set set1) (Set set2) = DataFlow.do
  (l, set1) <- withLinearly set1
  Set $ Ref.new (Raw.union (freeRef set1) (freeRef set2)) l
