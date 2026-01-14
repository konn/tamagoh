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

import Control.Functor.Linear (asks, runReader, runState, state)
import Control.Functor.Linear qualified as Control
import Control.Lens ()
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Monad.Borrow.Pure.Orphans ()
import Control.Monad.Borrow.Pure.Utils (swapTuple, unsafeLeak)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.Bits ((.&.))
import Data.Coerce (coerce)
import Data.DList qualified as DL
import Data.Foldable qualified as P
import Data.Generics.Labels ()
import Data.Hashable (Hashable (..))
import Data.Linear.Witness.Compat
import Data.Semigroup (Max (..))
import Data.Strict.Maybe qualified as Strict
import Data.Unrestricted.Linear qualified as Ur
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as MG
import Data.Vector.Mutable.Linear qualified as LV
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import Data.Word (Word8)
import GHC.Base (Type, UnliftedType)
import GHC.Generics (Generic)
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

data Entry k v where
  Entry :: k -> v %1 -> Entry k v
  deriving (Show, P.Functor)

instance (Consumable v) => Consumable (Entry k v) where
  consume (Entry _ v) = consume v
  {-# INLINE consume #-}

instance (Dupable v) => Dupable (Entry k v) where
  dup2 (Entry k v) =
    let %1 !(v1, v2) = dup2 v
     in (Entry k v1, Entry k v2)
  {-# INLINE dup2 #-}

newtype IndexInfo = IndexInfo Word8
  deriving (Show, Generic)
  deriving newtype (G.Vector U.Vector, MG.MVector U.MVector)
  deriving anyclass (U.Unbox)

newtype instance U.Vector IndexInfo = V_IndexInfo (U.Vector Word8)

newtype instance U.MVector s IndexInfo = MV_IndexInfo (U.MVector s Word8)

viewIndexInfo :: IndexInfo %1 -> Maybe DIB
viewIndexInfo = Unsafe.toLinear \(IndexInfo dib) ->
  if dib .&. 0b1000_0000 P.== 0
    then Just (DIB dib)
    else Nothing

pattern Present :: DIB -> IndexInfo
pattern Present dib <- (viewIndexInfo -> Just dib)
  where
    Present (DIB dib) = IndexInfo dib

decrement :: IndexInfo -> IndexInfo
{-# INLINE decrement #-}
decrement Absent = Absent
decrement p = coerce (P.- (1 :: Word8)) p

isStopIndex :: IndexInfo -> P.Bool
isStopIndex (IndexInfo dib) = dib .&. 0b0111_1111 P.== 0

pattern Absent :: IndexInfo
pattern Absent = IndexInfo (0b1000_0000)

{-# COMPLETE Present, Absent #-}

data HashMap k v where
  HashMap ::
    -- | Size
    {-# UNPACK #-} !Int ->
    -- | Capacity
    {-# UNPACK #-} !Int ->
    -- | An over-approximation of maximum DIB
    {-# UNPACK #-} !(Max DIB) ->
    -- | DIBs
    {-# UNPACK #-} !(LUV.Vector IndexInfo) %1 ->
    -- | Key-Value pairs
    !(KVs k v) %1 ->
    HashMap k v

instance Consumable (HashMap k v) where
  consume (HashMap _ _ _ idcs kvs) = idcs `lseq` consume kvs
  {-# INLINE consume #-}

instance Dupable (HashMap k v) where
  dup2 (HashMap size capa maxDIB idcs kvs) =
    let %1 !(idcs1, idcs2) = dup idcs
        %1 !(kvs1, kvs2) = dup kvs
     in (HashMap size capa maxDIB idcs1 kvs1, HashMap size capa maxDIB idcs2 kvs2)
  {-# INLINE dup2 #-}

deepClone :: forall k v. (Dupable v) => HashMap k v %1 -> (HashMap k v, HashMap k v)
deepClone = Unsafe.toLinear \dic@(HashMap size capa maxDIB idcs kvs) ->
  withLinearly kvs & Unsafe.toLinear \(lin, kvs) ->
    let go :: Int -> KVs k v %1 -> KVs k v
        go !i !acc
          | i >= capa = acc
          | otherwise = case LUV.unsafeGet i idcs of
              (Ur Absent, _) -> go (i + 1) acc
              (Ur _, _) ->
                LV.unsafeGet i kvs & \(Ur (Strict.fromJust -> (Entry k v)), _) ->
                  dupLeak v & \v' ->
                    go (i + 1) (LV.unsafeSet i (Strict.Just (Entry k v')) acc)
        kvs2 = go 0 (LV.constantL capa Strict.Nothing (fromPB lin))
     in (dic, HashMap size capa maxDIB (dupLeak idcs) kvs2)

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

-- NOTE: although we can use the first bit of 'IndexInfo' to indicate absence,
-- but we are still using a 'Maybe' wrapper around 'Entry' to store KVs for
-- the better performance in 'foldMapWithKey' - otherwise it would perform
-- drastically worse because it has to read 'IndexInfo' and 'KVs' vectors in mixture.
type KVs k v = LV.Vector (Strict.Maybe (Entry k v))

maxLoadFactor :: P.Double
maxLoadFactor = 0.75

maxDibLimit :: DIB
maxDibLimit = 127

new :: Int -> Linearly %1 -> HashMap k v
new capa = runReader Control.do
  let !capa' = 2 ^ intLog2' (2 * (max 1 capa) - 1)
      !physCapa = capa' + fromIntegral maxDibLimit
  indices <- asks $ LUV.constantL physCapa Absent . fromPB
  kvs <- asks $ LV.constantL physCapa Strict.Nothing . fromPB
  Control.pure $ HashMap 0 capa' 0 indices kvs

foldMapWithKey ::
  forall w k v.
  (Monoid w) =>
  (k -> v -> w) ->
  HashMap k v %1 ->
  w
foldMapWithKey f (HashMap size capa _ idcs kvs) = idcs `lseq` go 0 0 kvs mempty
  where
    physCapa = capa + fromIntegral maxDibLimit
    go :: Int -> Int -> KVs k v %1 -> w -> w
    go !i !count !kvs !acc
      | count == size || i == physCapa = kvs `lseq` acc
      | otherwise =
          LV.unsafeGet i kvs & \case
            (Ur (Strict.Just (Entry k v)), kvs) ->
              go (i + 1) (count + 1) kvs (acc <> f k v)
            (Ur Strict.Nothing, kvs) ->
              go (i + 1) count kvs acc

insert :: (Hashable k) => k -> v -> HashMap k v %1 -> (Ur (Maybe v), HashMap k v)
insert k v =
  swapTuple
    . flip runState (Ur (Just v))
    . alterF (\mval -> state \newVal -> (newVal, Ur mval)) k

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
          hm & \(HashMap size capa maxDIB idcs kvs) -> DataFlow.do
            kvs <- LV.unsafeSet loc.foundAt (Strict.Just (Entry k v)) kvs
            HashMap size capa maxDIB idcs kvs

size :: HashMap k v %1 -> (Ur Int, HashMap k v)
{-# INLINE size #-}
size (HashMap sz capa maxDIB idcs kvs) = (Ur sz, HashMap sz capa maxDIB idcs kvs)

capacity :: HashMap k v %1 -> (Ur Int, HashMap k v)
{-# INLINE capacity #-}
capacity (HashMap sz capa maxDIB idcs kvs) = (Ur capa, HashMap sz capa maxDIB idcs kvs)

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
          hm & \(HashMap size capa maxDIB idcs kvs) -> DataFlow.do
            kvs <- LV.unsafeSet loc.foundAt (Strict.Just (Entry k v)) kvs
            HashMap size capa maxDIB idcs kvs

deleteFrom :: Location v -> HashMap k v %1 -> HashMap k v
deleteFrom Location {..} (HashMap size capa maxDIB idcs kvs) = go foundAt idcs kvs
  where
    physMax = capa + fromIntegral maxDibLimit - 1
    go :: Int -> LUV.Vector IndexInfo %1 -> KVs k v %1 -> HashMap k v
    go !i !idcs !kvs
      | i == physMax = DataFlow.do
          idcs <- LUV.unsafeSet i Absent idcs
          kvs <- LV.unsafeSet i Strict.Nothing kvs
          HashMap (size - 1) capa maxDIB idcs kvs
      | otherwise =
          case LUV.unsafeGet (i + 1) idcs of
            (Ur ixi, idcs)
              | isStopIndex ixi -> DataFlow.do
                  -- Reaches the stop bucket: empty or DIB = 0.
                  -- By invariants, all emtpy buckets MUST have DIB = 0,
                  -- so we can just check dib of the next bucket.
                  idcs <- LUV.unsafeSet i Absent idcs
                  kvs <- LV.unsafeSet i Strict.Nothing kvs
                  HashMap (size - 1) capa maxDIB idcs kvs
              | otherwise -> DataFlow.do
                  -- Need to shift back
                  kvs <- unsafeSwapBoxed i (i + 1) kvs
                  idcs <- unsafeSwapUnboxed i (i + 1) idcs
                  -- Decrement DIB
                  idcs <- LUV.modify_ decrement i idcs
                  go (i + 1) idcs kvs

unsafeSwapBoxed :: Int -> Int -> LV.Vector a %1 -> LV.Vector a
unsafeSwapBoxed i j vec =
  LV.unsafeGet i vec & \(Ur xi, vec) ->
    LV.unsafeGet j vec & \(Ur xj, vec) -> DataFlow.do
      vec <- LV.unsafeSet i xj vec
      LV.unsafeSet j xi vec

unsafeSwapUnboxed :: (U.Unbox a) => Int -> Int -> LUV.Vector a %1 -> LUV.Vector a
unsafeSwapUnboxed i j vec =
  LUV.unsafeGet i vec & \(Ur xi, vec) ->
    LUV.unsafeGet j vec & \(Ur xj, vec) -> DataFlow.do
      vec <- LUV.unsafeSet i xj vec
      LUV.unsafeSet j xi vec

probeForInsert ::
  forall k v.
  (Hashable k) =>
  k -> v -> ProbeSuspended -> HashMap k v %1 -> HashMap k v
probeForInsert !k !v ProbeSuspended {..} (HashMap size capa maxDIB idcs kvs)
  | dibAtMiss P.> maxDibLimit || fromIntegral (size + 1) / fromIntegral capa >= maxLoadFactor = grow (Entry k v) idcs kvs
  | otherwise =
      case endType of
        Vacant -> DataFlow.do
          idcs <- LUV.unsafeSet offset (Present dibAtMiss) idcs
          kvs <- LV.unsafeSet offset (Strict.Just (Entry k v)) kvs
          HashMap (size + 1) capa (maxDIB P.<> Max dibAtMiss) idcs kvs
        Paused -> DataFlow.do
          go maxDIB dibAtMiss (Entry k v) offset idcs kvs
  where
    grow :: Entry k v -> LUV.Vector IndexInfo %1 -> KVs k v %1 -> HashMap k v
    grow (Entry !k !v) idcs kvs =
      withLinearly kvs & \(lin, kvs) ->
        case toList (HashMap size capa maxDIB idcs kvs) of
          Ur lst ->
            let !newCapa = capa * 2
             in insertMany ((k, v) : lst) (new newCapa lin)
    physCapa = capa + fromIntegral maxDibLimit

    go ::
      Max DIB ->
      DIB ->
      Entry k v ->
      Int ->
      LUV.Vector IndexInfo %1 ->
      KVs k v %1 ->
      HashMap k v
    -- Invariant: curMaxDIB <= maxDIBLimit
    -- Invariant: newDIB <= maxDibLimit
    go !curMaxDIB !newDib !newEntry !i !idcs !kvs
      | i == physCapa = grow newEntry idcs kvs
      | otherwise =
          LUV.unsafeGet i idcs & \case
            (Ur Absent, idcs) ->
              -- Found a vacant spot
              DataFlow.do
                !idcs <- LUV.unsafeSet i (Present newDib) idcs
                !kvs <- LV.unsafeSet i (Strict.Just newEntry) kvs
                HashMap (size + 1) capa (curMaxDIB P.<> Max newDib) idcs kvs
            (Ur (Present existingDib), idcs) ->
              -- Occupied, need to compare DIBs
              if existingDib P.< newDib
                then
                  LV.unsafeGet i kvs & \(Ur (Strict.fromJust -> nextEntry), kvs) ->
                    DataFlow.do
                      -- Takes from the rich and gives to the poor
                      !idcs <- LUV.unsafeSet i (Present newDib) idcs
                      !kvs <- LV.unsafeSet i (Strict.Just newEntry) kvs
                      -- existingDib < newDib
                      -- <==> existingDib +1 <= newDib <= maxDibLimit
                      -- hence the invariant met.
                      go (Max newDib P.<> curMaxDIB) (existingDib + 1) nextEntry (i + 1) idcs kvs
                else
                  if newDib P.== maxDibLimit P.- 1
                    then grow newEntry idcs kvs
                    else go curMaxDIB (newDib + 1) newEntry (i + 1) idcs kvs

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
  swapTuple
    . flip runState (Ur Nothing)
    . alterF (\old -> state \new -> (new, Ur old)) k

type Location :: Type -> UnliftedType
data Location v = Location
  { foundAt :: !Int
  , indexInfo :: {-# UNPACK #-} !IndexInfo
  , val :: !v
  }

type LookupResult :: Type -> UnliftedType
data LookupResult v where
  Found :: !(Location v) -> LookupResult v
  NotFound :: {-# UNPACK #-} !ProbeSuspended -> LookupResult v

type ProbeSuspended :: UnliftedType
data ProbeSuspended = ProbeSuspended
  { initialBucket :: {-# UNPACK #-} !Int
  , offset :: {-# UNPACK #-} !Int
  , endType :: !EndType
  , dibAtMiss :: {-# UNPACK #-} !DIB
  }

newtype EndType = EndType (# (# #) | (# #) #)

pattern Vacant :: EndType
pattern Vacant = EndType (# (# #) | #)

pattern Paused :: EndType
pattern Paused = EndType (# | (# #) #)

{-# COMPLETE Paused, Vacant #-}

probeKeyForAlter :: (Hashable k) => k -> HashMap k v %1 -> (# LookupResult v, HashMap k v #)
probeKeyForAlter k (HashMap size capa maxDIB idcs kvs) =
  go start 0 idcs kvs
  where
    !start = hash k `mod` capa
    !physCapa = capa + fromIntegral maxDibLimit
    go :: Int -> DIB -> LUV.Vector IndexInfo %1 -> KVs _ _ %1 -> (# LookupResult _, HashMap _ _ #)
    go !idx !dib !idcs !kvs
      | idx == physCapa || dib P.== maxDibLimit + 1 =
          (#
            NotFound
              ProbeSuspended
                { initialBucket = start
                , offset = idx
                , endType = Paused
                , dibAtMiss = dib
                }
            , HashMap size capa maxDIB idcs kvs
          #)
      | dib P.> maxDIB.getMax =
          LUV.unsafeGet idx idcs & \(Ur p, idcs) ->
            let endType = case p of
                  Absent -> Vacant
                  _ -> Paused
             in (#
                  NotFound
                    ProbeSuspended
                      { initialBucket = start
                      , offset = idx
                      , endType
                      , dibAtMiss = dib
                      }
                  , HashMap size capa maxDIB idcs kvs
                #)
      | otherwise =
          LUV.unsafeGet idx idcs & \case
            (Ur Absent, idcs) ->
              (#
                NotFound
                  ProbeSuspended
                    { initialBucket = start
                    , offset = idx
                    , endType = Vacant
                    , dibAtMiss = dib
                    }
                , HashMap size capa maxDIB idcs kvs
              #)
            (Ur indexInfo@(Present existingDib), idcs) ->
              LV.unsafeGet idx kvs & \(Ur (Strict.fromJust -> (Entry k' val)), kvs) ->
                if
                  | k P.== k' ->
                      (#
                        Found Location {foundAt = idx, ..}
                        , HashMap size capa maxDIB idcs kvs
                      #)
                  | existingDib P.< dib ->
                      (#
                        NotFound
                          ProbeSuspended
                            { initialBucket = start
                            , offset = idx
                            , endType = Paused
                            , dibAtMiss = dib
                            }
                        , HashMap size capa maxDIB idcs kvs
                      #)
                  | otherwise -> go (idx + 1) (dib + 1) idcs kvs

toList :: HashMap k v %1 -> Ur [(k, v)]
{-# INLINE toList #-}
toList = Ur.lift DL.toList . foldMapWithKey (curry $ Ur P.. DL.singleton)

fromList :: (Hashable k) => [(k, v)] -> Linearly %1 -> HashMap k v
fromList kvs =
  appEndo
    ( getDual $
        P.foldMap'
          (\(!k, !v) -> Dual $ Endo $ uncurry lseq . insert k v)
          kvs
    )
    . new (floor $ fromIntegral (P.length kvs) * maxLoadFactor)
