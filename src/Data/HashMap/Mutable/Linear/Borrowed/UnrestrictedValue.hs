{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- |
A borrowed HashMap with unrestricted (immutable) keys and values.

The table itself now lives upstream, as
"Data.HashMap.RobinHood.Mutable.Linear.Borrow"; this module is the thin
adapter tamagoh consumes it through. It exists for two reasons:

* upstream's queries thread the borrow back to the caller, in the style of
  @Data.Vector.Mutable.Linear.Borrow@, whereas tamagoh's call sites pass a
  fresh projection per query and want only the answer. The wrappers here drop
  the returned borrow, which is exactly what the pre-upstreaming API did.

* the 'Display' instance depends on "Text.Show.Borrowed", which is tamagoh's
  own class and so cannot be declared upstream.

Unlike "Data.HashMap.Mutable.Linear.Borrowed", this variant does not support
linear/mutable values. Both keys and values must be unrestricted.
-}
module Data.HashMap.Mutable.Linear.Borrowed.UnrestrictedValue (
  HashMapUr,
  Keyed,

  -- * Construction
  empty,
  fromList,

  -- * Mutation
  insert,
  InsertPlan,
  lookupForInsert,
  unsafeInsertPrepared,
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
  extend,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Function qualified as P
import Data.HashMap.Mutable.Linear (Keyed)
import Data.HashMap.RobinHood.Mutable.Linear.Borrow (
  InsertPlan,
  alter,
  alterF,
  delete,
  empty,
  extend,
  fromList,
  insert,
  swap,
  take,
  take_,
  union,
  unsafeInsertPrepared,
 )
import Data.HashMap.RobinHood.Mutable.Linear.Borrow qualified as Raw
import Data.List qualified as P
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, take)
import Text.Show.Borrowed (Display (..))

-- | A mutable HashMap with unrestricted keys and values.
type HashMapUr = Raw.HashMap

{- | Answer a query and discard the borrow it threaded back.

The borrow returned by an upstream query is the occurrence that was passed in,
so dropping it here leaves the caller exactly where the pre-upstreaming API
left them: having spent one occurrence on the query.
-}
answering ::
  (Consumable (Borrow bk α (HashMapUr k v))) =>
  BO α (Ur a, Borrow bk α (HashMapUr k v)) %1 ->
  BO α (Ur a)
{-# INLINE answering #-}
answering =
  Control.fmap \(Ur !answer, dic) -> consume dic `lseq` Ur answer

-- * Query

{-# INLINE size #-}
size :: Borrow bk α (HashMapUr k v) %1 -> BO α (Ur Int)
size = answering . Raw.size

{-# INLINE lookup #-}
lookup :: (Keyed k) => k -> Borrow bk α (HashMapUr k v) %1 -> BO α (Ur (Maybe v))
lookup key = answering . Raw.lookup key

{-# INLINE member #-}
member :: (Keyed k) => k -> Borrow bk α (HashMapUr k v) %1 -> BO α (Ur Bool)
member key = answering . Raw.member key

{-# INLINE lookupForInsert #-}
lookupForInsert ::
  (Keyed k) =>
  k ->
  Borrow bk α (HashMapUr k v) %1 ->
  BO α (Ur (Either v (InsertPlan k)))
lookupForInsert key = answering . Raw.lookupForInsert key

-- * Iteration

{-# INLINE toList #-}
toList :: Borrow bk α (HashMapUr k v) %1 -> BO α (Ur [(k, v)])
toList = answering . Raw.toList

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
