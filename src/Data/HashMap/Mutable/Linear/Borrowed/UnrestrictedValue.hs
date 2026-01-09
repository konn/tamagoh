{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
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
import Control.Monad.Borrow.Pure.Internal
import Control.Monad.Borrow.Pure.Utils (coerceLin, unsafeLeak)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Array.Mutable.Linear qualified as Array
import Data.Bifunctor.Linear qualified as Bi
import Data.Coerce (coerce)
import Data.DList (DList)
import Data.DList qualified as DL
import Data.Function qualified as P
import Data.Functor.Linear qualified as Data
import Data.HashMap.Mutable.Linear (Keyed)
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Internal qualified as Raw
import Data.HashMap.Mutable.Linear.Witness qualified as Raw
import Data.Linear.Witness.Compat (fromPB)
import Data.List qualified as P
import Data.Ref.Linear (freeRef)
import Data.Ref.Linear qualified as Ref
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, take)
import Text.Show.Borrowed (Display (..))
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

{- | A mutable HashMap with unrestricted keys and values.
The constructor is not exported to maintain invariants.
-}
newtype HashMapUr k v = HM (Ref (Raw.HashMap k v))
  deriving newtype (LinearOnly)

instance Consumable (HashMapUr k v) where
  consume = \(HM ref) -> consume $ freeRef ref
  {-# INLINE consume #-}

-- | Dupable instance without deep cloning (values are unrestricted).
instance Dupable (HashMapUr k v) where
  {-# NOINLINE dup2 #-}
  dup2 = Unsafe.toLinear \(HM !ref) -> DataFlow.do
    (lin, !ref) <- withLinearly ref
    (ref, !hm) <- Unsafe.toLinear (\ref -> (ref, freeRef ref)) ref
    !hm' <- Unsafe.toLinear (\(!_, !hm') -> hm') $ dup hm
    (HM ref, HM $! Ref.new hm' lin)

-- | Copyable instance without deep cloning (values are unrestricted).
instance Copyable (HashMapUr k v) where
  copy = Unsafe.toLinear \(UnsafeAlias (HM !ref)) -> DataFlow.do
    (lin, !ref) <- withLinearly ref
    !hm <- freeRef ref
    !hm' <- Unsafe.toLinear (\(!_, !hm') -> hm') $ dup hm
    HM $! Ref.new hm' lin

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

-- * Internal helpers

inner :: HashMapUr k v %1 -> Ref (Raw.HashMap k v)
inner = Unsafe.toLinear \ !a -> coerce a

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
    Ur (UnsafeAlias !dic) <- readSharedRef (coerceBor dic)
    case f dic of
      -- NOTE: This @dic@ is RAW memory block,
      -- so we MUST NOT 'consume' it here, and instead just intentionally leak it.
      -- This leakage won't cause memory leak, because Lender will eventually free the whole block.
      (!res, !dic) -> unsafeLeak dic `lseq` Control.pure res

askRaw_ ::
  (Raw.HashMap k v %1 -> a) %1 ->
  Borrow bk α (HashMapUr k v) %m ->
  BO α a
{-# INLINE askRaw_ #-}
askRaw_ f dic = case share dic of
  Ur !dic -> Control.do
    Ur (UnsafeAlias !dic) <- readSharedRef (coerceBor dic)
    case f dic of
      !res -> Control.pure res

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

-- * Iteration

{- | Convert the HashMap to a list. Uses tail-recursive implementation
with strict accumulator to avoid thunks.
-}
toList :: Borrow bk α (HashMapUr k v) %m -> BO α (Ur [(k, v)])
toList = askRaw_ rawToList'

-- Almost same as 'Raw.toList', but it uses DList and tail-recursion and forces
-- thunks to avoid mutation after read.
rawToList' :: Raw.HashMap k v %1 -> Ur [(k, v)]
{-# INLINE rawToList' #-}
rawToList' = \(Raw.HashMap _ n !robinArr) ->
  let go :: Int -> Array.Array _ %1 -> DList (k, v) -> Ur [(k, v)]
      go !i !arr !acc
        | i < n =
            Array.unsafeGet i arr & \case
              (Ur (Just (Raw.RobinVal !_ !k !v)), !arr) ->
                go (i + 1) arr (DL.snoc acc (k, v))
              (Ur Nothing, !arr) -> go (i + 1) arr acc
        | otherwise = unsafeLeak arr `lseq` Ur (DL.toList acc)
   in go 0 robinArr P.mempty

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
