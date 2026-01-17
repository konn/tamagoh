{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedDatatypes #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.HashMap.RobinHood.Mutable.Linear (
  HashMap,
  Hashable,
  new,
  fromList,
  insert,
  insertMany,
  foldMapWithKey,
  toList,
  lookup,
  member,
  union,
  delete,
  alter,
  alterF,
  size,
  capacity,

  -- * Internal types
  deepClone,
) where

import Control.Functor.Linear (asks, runReader)
import Control.Functor.Linear qualified as Control
import Control.Lens ()
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Monad.Borrow.Pure.Orphans ()
import Control.Monad.Borrow.Pure.Utils (unsafeLeak)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Bits ((.&.))
import Data.DList qualified as DL
import Data.Foldable qualified as P
import Data.Functor.Linear qualified as Data
import Data.Generics.Labels ()
import Data.Hashable (Hashable (..))
import Data.Linear.Witness.Compat
import Data.Semigroup (Max (..))
import Data.Unrestricted.Linear qualified as Ur
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as MG
import Data.Vector.Mutable.Linear qualified as LV
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Unboxed qualified as U
import Data.Word (Word8)
import GHC.Base (Type, UnliftedType)
import GHC.TypeError (ErrorMessage (..), Unsatisfiable, unsatisfiable)
import Math.NumberTheory.Logarithms (intLog2')
import Prelude.Linear hiding (insert, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

-- Difference from Initial Bucket
newtype DIB = DIB Word8
  deriving newtype (P.Eq, P.Ord, P.Num, P.Enum, Additive, Show, Hashable, Consumable, Dupable, Movable, P.Real, P.Integral)
  deriving newtype (G.Vector U.Vector, MG.MVector U.MVector)
  deriving anyclass (U.Unbox)

newtype instance U.Vector DIB = V_DIB (U.Vector Word8)

newtype instance U.MVector s DIB = MV_DIB (U.MVector s Word8)

-- | Cached hash value for fast comparison and rehashing
newtype Fingerprint = Fingerprint Int
  deriving newtype (P.Eq, P.Ord, Show, Consumable, Dupable, Movable)

-- | Compute fingerprint from hashable key
{-# INLINE fingerprint #-}
fingerprint :: (Hashable k) => k -> Fingerprint
fingerprint = Fingerprint P.. hash

-- | Get bucket index from fingerprint and capacity (must be power of 2)
{-# INLINE fingerprintBucket #-}
fingerprintBucket :: Fingerprint -> Int -> Int
fingerprintBucket (Fingerprint h) capa = h .&. (capa - 1)

-- | A slot in the hash table, combining fingerprint, DIB with key-value pair
data Slot k v where
  Empty :: Slot k v
  Occupied :: {-# UNPACK #-} !Fingerprint -> {-# UNPACK #-} !DIB -> !k -> !v %1 -> Slot k v
  deriving (Show)

instance (Consumable v) => Consumable (Slot k v) where
  consume Empty = ()
  consume (Occupied _ _ _ v) = consume v
  {-# INLINE consume #-}

instance (Dupable v) => Dupable (Slot k v) where
  dup2 Empty = (Empty, Empty)
  dup2 (Occupied fp dib k v) =
    let !(v1, v2) = dup2 v
     in (Occupied fp dib k v1, Occupied fp dib k v2)
  {-# INLINE dup2 #-}

{-# INLINE isStopSlot #-}
isStopSlot :: Slot k v -> P.Bool
isStopSlot Empty = P.True
isStopSlot (Occupied _ dib _ _) = dib P.== 0

{-# INLINE decrementSlot #-}
decrementSlot :: Slot k v %1 -> Slot k v
decrementSlot Empty = Empty
decrementSlot (Occupied fp dib k v) = Occupied fp (dib P.- 1) k v

{-# INLINE slotDIB #-}
slotDIB :: Slot k v -> Maybe DIB
slotDIB Empty = Nothing
slotDIB (Occupied _ dib _ _) = Just dib

data HashMap k v where
  HashMap ::
    -- | Size
    {-# UNPACK #-} !Int ->
    -- | Capacity
    {-# UNPACK #-} !Int ->
    -- | An over-approximation of maximum DIB
    {-# UNPACK #-} !(Max DIB) ->
    -- | Slots (unified DIB + key-value)
    !(Slots k v) %1 ->
    HashMap k v

instance Consumable (HashMap k v) where
  consume (HashMap _ _ _ slots) = consume slots
  {-# INLINE consume #-}

instance Dupable (HashMap k v) where
  dup2 (HashMap size capa maxDIB slots) =
    let %1 !(slots1, slots2) = dup slots
     in (HashMap size capa maxDIB slots1, HashMap size capa maxDIB slots2)
  {-# INLINE dup2 #-}

deepClone :: forall k v. (Dupable v) => HashMap k v %1 -> (HashMap k v, HashMap k v)
deepClone = Unsafe.toLinear \dic@(HashMap size capa maxDIB slots) ->
  withLinearly slots & \(lin, slots) ->
    let go :: Int -> Slots k v %1 -> Slots k v
        go !i !acc
          | i >= capa = acc
          | otherwise = case LV.unsafeGet i slots of
              (Ur Empty, _) -> go (i + 1) acc
              (Ur (Occupied fp dib k v), _) ->
                dupLeak v & \v' ->
                  go (i + 1) (LV.unsafeSet i (Occupied fp dib k v') acc)
        slots2 = go 0 (LV.constantL (capa + fromIntegral maxDibLimit) Empty (fromPB lin))
     in (dic, HashMap size capa maxDIB slots2)

dupLeak :: (Dupable a) => a %1 -> a
dupLeak x =
  let %1 !(x1, x2) = dup x
   in unsafeLeak x1 `lseq` x2

instance
  (Unsatisfiable ('Text "HashMap is only usable in linear context")) =>
  Movable (HashMap k v)
  where
  move = unsatisfiable

instance LinearOnly (HashMap k v) where
  linearOnly = UnsafeLinearOnly

-- | Slots vector storing DIB and key-value together
type Slots k v = LV.Vector (Slot k v)

maxLoadFactor :: P.Double
maxLoadFactor = 0.75

maxDibLimit :: DIB
maxDibLimit = 127

new :: Int -> Linearly %1 -> HashMap k v
new capa = runReader Control.do
  let !capa' = 2 ^ intLog2' (2 * (max 1 capa) - 1)
      !physCapa = capa' + fromIntegral maxDibLimit
  slots <- asks $ LV.constantL physCapa Empty . fromPB
  Control.pure $ HashMap 0 capa' 0 slots

foldMapWithKey ::
  forall w k v.
  (Monoid w) =>
  (k -> v -> w) ->
  HashMap k v %1 ->
  w
foldMapWithKey f (HashMap size capa _ slots) = go 0 0 slots mempty
  where
    physCapa = capa + fromIntegral maxDibLimit
    go :: Int -> Int -> Slots k v %1 -> w -> w
    go !i !count !slots !acc
      | count == size || i == physCapa = slots `lseq` acc
      | otherwise =
          LV.unsafeGet i slots & \case
            (Ur (Occupied _ _ k v), slots') ->
              go (i + 1) (count + 1) slots' (acc <> f k v)
            (Ur Empty, slots') ->
              go (i + 1) count slots' acc

insert :: (Hashable k) => k -> v -> HashMap k v %1 -> (Ur (Maybe v), HashMap k v)
insert k v =
  unswapper
    . alterF (\mval -> Swapper (Ur (Just v)) mval) k

insertMany ::
  (Hashable k) =>
  [(k, v)] ->
  HashMap k v %1 ->
  HashMap k v
{-# INLINE insertMany #-}
insertMany kvs hm =
  appEndo
    ( getDual
        ( P.foldMap'
            (\(!k, !v) -> Dual $ Endo $ uncurry lseq . insert k v)
            kvs
        )
    )
    hm

alter ::
  forall k v.
  (Hashable k) =>
  (Maybe v -> Maybe v) ->
  k ->
  HashMap k v %1 ->
  HashMap k v
alter f k hm =
  case probeKeyForAlter k hm of
    (# NotFound st, hm #) ->
      -- not found!
      case f Nothing of
        Nothing -> hm -- No modification needed
        Just !v -> probeForInsert k v st hm
    -- Already inserted with older value.
    (# Found loc, hm #) ->
      case f (Just loc.val) of
        Nothing -> deleteFrom loc hm
        (Just !v) ->
          -- Update in place
          hm & \(HashMap size capa maxDIB slots) -> DataFlow.do
            slots <- LV.unsafeSet loc.foundAt (Occupied loc.slotFp loc.slotDIB k v) slots
            HashMap size capa maxDIB slots

size :: HashMap k v %1 -> (Ur Int, HashMap k v)
{-# INLINE size #-}
size (HashMap sz capa maxDIB slots) = (Ur sz, HashMap sz capa maxDIB slots)

capacity :: HashMap k v %1 -> (Ur Int, HashMap k v)
{-# INLINE capacity #-}
capacity (HashMap sz capa maxDIB slots) = (Ur capa, HashMap sz capa maxDIB slots)

union :: (Hashable k) => HashMap k v %1 -> HashMap k v %1 -> HashMap k v
{-# INLINE union #-}
union hm1 hm2 = case (size hm1, size hm2) of
  ((Ur sz1, hm1), (Ur sz2, hm2)) -> DataFlow.do
    (parent, child) <- if sz1 >= sz2 then (hm1, hm2) else (hm2, hm1)
    -- FIXME: favours the right-hand side when key collides
    appEndo
      (foldMapWithKey (\ !k !v -> Endo $ uncurry lseq . insert k v) child)
      parent

alterF ::
  (Hashable k, Control.Functor f) =>
  (Maybe v -> f (Ur (Maybe v))) %1 ->
  k ->
  HashMap k v %1 ->
  f (HashMap k v)
alterF f k hm =
  case probeKeyForAlter k hm of
    (# NotFound st, hm #) ->
      -- not found!
      f Nothing Control.<&> \case
        Ur Nothing -> hm -- No modification needed
        Ur (Just !v) -> probeForInsert k v st hm
    -- Already inserted with older value.
    (# Found loc, hm #) ->
      f (Just loc.val) Control.<&> \case
        Ur Nothing -> deleteFrom loc hm
        Ur (Just !v) ->
          -- Update in place
          hm & \(HashMap size capa maxDIB slots) -> DataFlow.do
            slots <- LV.unsafeSet loc.foundAt (Occupied loc.slotFp loc.slotDIB k v) slots
            HashMap size capa maxDIB slots

data Swapper v a where
  Swapper :: a %1 -> Maybe v -> Swapper v a

{-# INLINE unswapper #-}
unswapper :: Swapper v a %1 -> (Ur (Maybe v), a)
unswapper (Swapper l b) = (Ur b, l)

instance Data.Functor (Swapper v) where
  {-# SPECIALIZE instance Data.Functor (Swapper v) #-}
  fmap f = \(Swapper l b) -> Swapper (f l) (b :: Maybe v)
  {-# INLINE fmap #-}

instance Control.Functor (Swapper v) where
  {-# SPECIALIZE instance Control.Functor (Swapper v) #-}
  fmap f = \(Swapper l b) -> Swapper (f l) (b :: Maybe v)
  {-# INLINE fmap #-}

deleteFrom :: Location v -> HashMap k v %1 -> HashMap k v
deleteFrom Location {..} (HashMap size capa maxDIB slots) = go foundAt slots
  where
    physMax = capa + fromIntegral maxDibLimit - 1
    go :: Int -> Slots k v %1 -> HashMap k v
    go !i !slots
      | i == physMax = DataFlow.do
          slots <- LV.unsafeSet i Empty slots
          HashMap (size - 1) capa maxDIB slots
      | otherwise =
          LV.unsafeGet (i + 1) slots & \(Ur nextSlot, slots) ->
            if isStopSlot nextSlot
              then DataFlow.do
                -- Reaches the stop bucket: empty or DIB = 0.
                slots <- LV.unsafeSet i Empty slots
                HashMap (size - 1) capa maxDIB slots
              else DataFlow.do
                -- Need to shift back and decrement DIB
                slots <- LV.unsafeSet i (decrementSlot nextSlot) slots
                slots <- LV.unsafeSet (i + 1) Empty slots
                go (i + 1) slots

{-# INLINE probeForInsert #-}
probeForInsert ::
  forall k v.
  (Hashable k) =>
  k -> v -> ProbeSuspended -> HashMap k v %1 -> HashMap k v
probeForInsert !k !v ProbeSuspended {..} (HashMap size capa maxDIB slots)
  | dibAtMiss P.> maxDibLimit || fromIntegral (size + 1) / fromIntegral capa >= maxLoadFactor =
      grow size capa searchFp k v slots
  | otherwise = case endType of
      Vacant -> DataFlow.do
        slots <- LV.unsafeSet offset (Occupied searchFp dibAtMiss k v) slots
        HashMap (size + 1) capa (maxDIB P.<> Max dibAtMiss) slots
      Paused
        | offset == physCapa -> grow size capa searchFp k v slots
        | otherwise -> case cachedDIB of
            Nothing ->
              -- Found a vacant spot (shouldn't happen in Paused, but handle it)
              DataFlow.do
                slots <- LV.unsafeSet offset (Occupied searchFp dibAtMiss k v) slots
                HashMap (size + 1) capa (maxDIB P.<> Max dibAtMiss) slots
            Just existingDib ->
              if existingDib P.< dibAtMiss
                then
                  LV.unsafeGet offset slots & \case
                    (Ur (Occupied existingFp _ k' v'), slots) -> DataFlow.do
                      -- Takes from the rich and gives to the poor
                      slots <- LV.unsafeSet offset (Occupied searchFp dibAtMiss k v) slots
                      go size capa (Max dibAtMiss P.<> maxDIB) existingFp (existingDib + 1) k' v' (offset + 1) slots
                    (Ur Empty, slots) -> error "probeForInsert: impossible Empty slot" slots
                else
                  if dibAtMiss P.== maxDibLimit P.- 1
                    then grow size capa searchFp k v slots
                    else go size capa maxDIB searchFp (dibAtMiss + 1) k v (offset + 1) slots
  where
    physCapa :: Int
    physCapa = capa + fromIntegral maxDibLimit

    grow :: Int -> Int -> Fingerprint -> k -> v -> Slots k v %1 -> HashMap k v
    grow !size !capa !fp newK newV slots =
      withLinearly slots & \(lin, slots) ->
        rehashInto size physCapa fp newK newV 0 0 slots (new (capa * 2) lin)

    go ::
      Int ->
      Int ->
      Max DIB ->
      Fingerprint ->
      DIB ->
      k ->
      v ->
      Int ->
      Slots k v %1 ->
      HashMap k v
    -- Invariant: curMaxDIB <= maxDIBLimit
    -- Invariant: newDIB <= maxDibLimit
    go !size !capa !curMaxDIB !newFp !newDib !newK !newV !i !slots =
      if i == physCapa
        then grow size capa newFp newK newV slots
        else
          LV.unsafeGet i slots
            & \case
              (Ur Empty, slots) ->
                -- Found a vacant spot
                DataFlow.do
                  slots <- LV.unsafeSet i (Occupied newFp newDib newK newV) slots
                  HashMap (size + 1) capa (curMaxDIB P.<> Max newDib) slots
              (Ur (Occupied existingFp existingDib k' v'), slots) ->
                -- Occupied, need to compare DIBs
                if existingDib P.< newDib
                  then DataFlow.do
                    -- Takes from the rich and gives to the poor
                    slots <- LV.unsafeSet i (Occupied newFp newDib newK newV) slots
                    -- existingDib < newDib
                    -- <==> existingDib +1 <= newDib <= maxDibLimit
                    -- hence the invariant met.
                    go size capa (Max newDib P.<> curMaxDIB) existingFp (existingDib + 1) k' v' (i + 1) slots
                  else
                    if newDib P.== maxDibLimit P.- 1
                      then grow size capa newFp newK newV slots
                      else go size capa curMaxDIB newFp (newDib + 1) newK newV (i + 1) slots

{- | Fast insertion when we know key doesn't exist (used during rehash).
Skips key equality checks since all keys are guaranteed unique.
-}
{-# INLINE insertFresh #-}
insertFresh :: (Hashable k) => k -> v -> HashMap k v %1 -> HashMap k v
insertFresh !k = insertFreshWithFingerprint (fingerprint k) k

-- | Fast insertion with pre-computed fingerprint (avoids rehashing during rehashInto)
{-# INLINE insertFreshWithFingerprint #-}
insertFreshWithFingerprint :: Fingerprint -> k -> v -> HashMap k v %1 -> HashMap k v
insertFreshWithFingerprint !fp !k !v (HashMap size capa maxDIB slots) =
  let !start = fingerprintBucket fp capa
      !physCapa = capa + fromIntegral maxDibLimit
   in goFreshF size capa physCapa maxDIB 0 fp k v start slots

-- | Internal loop for insertFreshWithFingerprint - probes for empty slot or Robin Hood displacement
goFreshF ::
  Int -> -- size
  Int -> -- capa
  Int -> -- physCapa
  Max DIB -> -- current max DIB
  DIB -> -- current DIB for entry being inserted
  Fingerprint -> -- fingerprint of entry being inserted
  k ->
  v ->
  Int -> -- current index
  Slots k v %1 ->
  HashMap k v
goFreshF !size !capa !physCapa !curMaxDIB !dib !fp !k !v !i !slots
  | i == physCapa || dib P.> maxDibLimit =
      -- Need to grow - this shouldn't happen during normal rehash
      -- but handle it for safety
      withLinearly slots & \(lin, slots) ->
        slots `lseq` insertFreshWithFingerprint fp k v (new (capa * 2) lin)
  | otherwise =
      LV.unsafeGet i slots & \case
        (Ur Empty, slots') -> DataFlow.do
          -- Found empty slot, insert here
          slots' <- LV.unsafeSet i (Occupied fp dib k v) slots'
          HashMap (size + 1) capa (curMaxDIB P.<> Max dib) slots'
        (Ur (Occupied existingFp existingDib k' v'), slots') ->
          if existingDib P.< dib
            then DataFlow.do
              -- Robin Hood: displace the existing entry
              slots' <- LV.unsafeSet i (Occupied fp dib k v) slots'
              goFreshF size capa physCapa (curMaxDIB P.<> Max dib) (existingDib + 1) existingFp k' v' (i + 1) slots'
            else
              -- Keep probing
              goFreshF size capa physCapa curMaxDIB (dib + 1) fp k v (i + 1) slots'

-- | Direct rehash: iterate over old slots and insert into new map
rehashInto ::
  Int -> -- size of old map
  Int -> -- physCapa of old map
  Fingerprint -> -- fingerprint of key to insert
  k -> -- key to insert
  v -> -- value to insert
  Int -> -- current index
  Int -> -- count of elements processed
  Slots k v %1 ->
  HashMap k v %1 ->
  HashMap k v
rehashInto !oldSize !oldPhysCapa !fp !k !v !i !count !oldSlots !newMap
  | count == oldSize || i >= oldPhysCapa =
      -- Done iterating old map, insert the new entry and consume old slots
      oldSlots `lseq` insertFreshWithFingerprint fp k v newMap
  | otherwise =
      LV.unsafeGet i oldSlots & \case
        (Ur (Occupied fp' _ k' v'), oldSlots') ->
          -- Found an entry, insert it into new map using cached fingerprint
          rehashInto oldSize oldPhysCapa fp k v (i + 1) (count + 1) oldSlots' (insertFreshWithFingerprint fp' k' v' newMap)
        (Ur Empty, oldSlots') ->
          -- Empty slot, skip
          rehashInto oldSize oldPhysCapa fp k v (i + 1) count oldSlots' newMap

lookup :: (Hashable k) => k -> HashMap k v %1 -> (Ur (Maybe v), HashMap k v)
lookup k hm =
  case probeKeyForAlter k hm of
    (# NotFound _, hm #) -> (Ur Nothing, hm)
    (# Found !loc, hm #) -> (Ur (Just loc.val), hm)

member :: (Hashable k) => k -> HashMap k v %1 -> (Ur Bool, HashMap k v)
member k hm =
  case probeKeyForAlter k hm of
    (# NotFound {}, hm #) -> (Ur False, hm)
    (# Found {}, hm #) -> (Ur True, hm)

delete :: (Hashable k) => k -> HashMap k v %1 -> (Ur (Maybe v), HashMap k v)
{-# INLINE delete #-}
delete k =
  unswapper
    . alterF (\old -> Swapper (Ur Nothing) old) k

type Location :: Type -> UnliftedType
data Location v = Location
  { foundAt :: !Int
  , slotFp :: {-# UNPACK #-} !Fingerprint
  , slotDIB :: {-# UNPACK #-} !DIB
  , val :: !v
  }

type LookupResult :: Type -> UnliftedType
data LookupResult v where
  Found :: !(Location v) -> LookupResult v
  NotFound :: {-# UNPACK #-} !ProbeSuspended -> LookupResult v

type ProbeSuspended :: UnliftedType
data ProbeSuspended = ProbeSuspended
  { searchFp :: {-# UNPACK #-} !Fingerprint
  -- ^ Fingerprint of the key being searched/inserted
  , initialBucket :: {-# UNPACK #-} !Int
  , offset :: {-# UNPACK #-} !Int
  , endType :: !EndType
  , dibAtMiss :: {-# UNPACK #-} !DIB
  , cachedDIB :: !(Maybe DIB)
  -- ^ Nothing for Empty, Just dib for Occupied
  }

newtype EndType = EndType (# (# #) | (# #) #)

pattern Vacant :: EndType
pattern Vacant = EndType (# (# #) | #)

pattern Paused :: EndType
pattern Paused = EndType (# | (# #) #)

{-# COMPLETE Paused, Vacant #-}

{-# INLINE probeKeyForAlter #-}
probeKeyForAlter :: forall k v. (Hashable k) => k -> HashMap k v %1 -> (# LookupResult v, HashMap k v #)
probeKeyForAlter k (HashMap size capa maxDIB slots) =
  go start 0 slots
  where
    !searchFp = fingerprint k
    !start = fingerprintBucket searchFp capa
    !physCapa = capa + fromIntegral maxDibLimit
    go :: Int -> DIB -> Slots k v %1 -> (# LookupResult v, HashMap k v #)
    go !idx !dib !slots
      | idx == physCapa || dib P.== maxDibLimit + 1 =
          (#
            NotFound
              ProbeSuspended
                { searchFp
                , initialBucket = start
                , offset = idx
                , endType = Paused
                , dibAtMiss = dib
                , cachedDIB = Nothing -- dummy: always triggers grow
                }
            , HashMap size capa maxDIB slots
          #)
      | dib P.> maxDIB.getMax =
          LV.unsafeGet idx slots & \(Ur slot, slots) ->
            let endType = case slot of
                  Empty -> Vacant
                  _ -> Paused
             in (#
                  NotFound
                    ProbeSuspended
                      { searchFp
                      , initialBucket = start
                      , offset = idx
                      , endType
                      , dibAtMiss = dib
                      , cachedDIB = slotDIB slot
                      }
                  , HashMap size capa maxDIB slots
                #)
      | otherwise =
          LV.unsafeGet idx slots & \case
            (Ur Empty, slots) ->
              (#
                NotFound
                  ProbeSuspended
                    { searchFp
                    , initialBucket = start
                    , offset = idx
                    , endType = Vacant
                    , dibAtMiss = dib
                    , cachedDIB = Nothing
                    }
                , HashMap size capa maxDIB slots
              #)
            (Ur (Occupied slotFp existingDib k' val), slots) ->
              if
                | existingDib P.< dib ->
                    -- Robin Hood early termination: key would have displaced this entry
                    (#
                      NotFound
                        ProbeSuspended
                          { searchFp
                          , initialBucket = start
                          , offset = idx
                          , endType = Paused
                          , dibAtMiss = dib
                          , cachedDIB = Just existingDib
                          }
                      , HashMap size capa maxDIB slots
                    #)
                | slotFp P./= searchFp -> go (idx + 1) (dib + 1) slots -- fast reject on hash mismatch
                | k P.== k' ->
                    (#
                      Found Location {foundAt = idx, slotFp, slotDIB = existingDib, val}
                      , HashMap size capa maxDIB slots
                    #)
                | otherwise -> go (idx + 1) (dib + 1) slots

toList :: HashMap k v %1 -> Ur [(k, v)]
{-# INLINE toList #-}
toList = Ur.lift DL.toList . foldMapWithKey (curry $ Ur P.. DL.singleton)

fromList :: (Hashable k) => [(k, v)] -> Linearly %1 -> HashMap k v
fromList kvs = insertMany kvs . new (P.length kvs)
