{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
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
  foldMapWithKey,
  toList,
  lookup,
  member,
  union,
  delete,
  alter,
  alterF,
  size,

  -- * Internal types
  deepClone,
) where

import Control.Functor.Linear (asks, execState, modify, runReader, runState, state)
import Control.Functor.Linear qualified as Control
import Control.Lens ((+~), (-~))
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Lifetime.Token.Internal
import Control.Monad.Borrow.Pure.Orphans ()
import Control.Monad.Borrow.Pure.Utils (swapTuple, unsafeLeak)
import Control.Syntax.DataFlow qualified as DataFlow
import Data.DList qualified as DL
import Data.FMList qualified as FML
import Data.Foldable qualified as P
import Data.Generics.Labels ()
import Data.Hashable (Hashable (..))
import Data.Linear.Witness.Compat
import Data.Strict.Maybe qualified as Strict
import Data.Unrestricted.Linear (UrT (..), runUrT)
import Data.Unrestricted.Linear qualified as Ur
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as MG
import Data.Vector.Mutable.Linear qualified as LV
import Data.Vector.Mutable.Linear.Extra qualified as LV
import Data.Vector.Mutable.Linear.Unboxed qualified as LUV
import Data.Vector.Unboxed qualified as U
import GHC.Generics (Generic)
import GHC.TypeError (ErrorMessage (..), Unsatisfiable, unsatisfiable)
import Math.NumberTheory.Logarithms (intLog2')
import Prelude.Linear hiding (insert, lookup)
import Unsafe.Linear qualified as Unsafe
import Prelude qualified as P

-- Difference from Initial Bucket
newtype DIB = DIB Word
  deriving newtype (P.Eq, P.Ord, P.Num, Additive, Show, Hashable, Consumable, Dupable, Movable)
  deriving newtype (G.Vector U.Vector, MG.MVector U.MVector)
  deriving anyclass (U.Unbox)

newtype instance U.Vector DIB = V_DIB (U.Vector Word)

newtype instance U.MVector s DIB = MV_DIB (U.MVector s Word)

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

data IndexInfo = IndexInfo
  { residual :: {-# UNPACK #-} !Int
  , dib :: {-# UNPACK #-} !DIB
  }
  deriving (Show, Generic)
  deriving (G.Vector U.Vector, MG.MVector U.MVector) via IndexInfo `U.As` (Int, DIB)
  deriving anyclass (U.Unbox)

instance U.IsoUnbox IndexInfo (Int, DIB)

newtype instance U.Vector IndexInfo = V_IndexInfo (U.Vector (Int, DIB))

newtype instance U.MVector s IndexInfo = MV_IndexInfo (U.MVector s (Int, DIB))

data HashMap k v where
  HashMap ::
    -- | Size
    {-# UNPACK #-} !Int ->
    -- | Capacity
    {-# UNPACK #-} !Int ->
    -- | An over-approximation of maximum DIB
    {-# UNPACK #-} !DIB ->
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
          | otherwise = case LV.unsafeGet i kvs of
              (Ur (Strict.Just (Entry k v)), _) ->
                dupLeak v & \v' ->
                  go (i + 1) (LV.unsafeSet i (Strict.Just (Entry k v')) acc)
              (Ur Strict.Nothing, _) -> go (i + 1) acc
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

type KVs k v = LV.Vector (Strict.Maybe (Entry k v))

maxLoadFactor :: P.Double
maxLoadFactor = 0.75

new :: Int -> Linearly %1 -> HashMap k v
new capa = runReader Control.do
  let capa' = 2 ^ intLog2' (2 * (max 1 capa) - 1)
  indices <- asks $ LUV.constantL capa' (IndexInfo 0 0) . fromPB
  kvs <- asks $ LV.constantL capa' Strict.Nothing . fromPB
  Control.pure $ HashMap 0 capa' (DIB 0) indices kvs

foldMapWithKey ::
  forall w k v.
  (Monoid w) =>
  (k -> v -> w) ->
  HashMap k v %1 ->
  w
foldMapWithKey f (HashMap size capa _ idcs kvs) = idcs `lseq` go 0 0 kvs mempty
  where
    go :: Int -> Int -> KVs k v %1 -> w -> w
    go !i !count !kvs !acc
      | count == size || i >= capa = kvs `lseq` acc
      | otherwise =
          LV.unsafeGet i kvs & \case
            (Ur Strict.Nothing, kvs) -> go (i + 1) count kvs acc
            (Ur (Strict.Just (Entry k v)), kvs) -> go (i + 1) (count + 1) kvs (acc <> f k v)

insert :: (Hashable k) => k -> v -> HashMap k v %1 -> (Ur (Maybe v), HashMap k v)
insert k v =
  swapTuple
    . flip runState (Ur (Just v))
    . alterF (\mval -> state \newVal -> (newVal, Ur mval)) k

alter ::
  forall k v.
  (Hashable k) =>
  (Maybe v -> Maybe v) ->
  k ->
  HashMap k v %1 ->
  HashMap k v
alter f k hm =
  probeKeyForAlter k hm & \case
    (Ur (NotFound st), hm) ->
      -- not found!
      case f Nothing of
        Nothing -> hm -- No modification needed
        Just !v -> probeForInsert k v st hm
    -- Already inserted with older value.
    (Ur (Found loc), hm) ->
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

union :: (Hashable k) => HashMap k v %1 -> HashMap k v %1 -> HashMap k v
{-# INLINE union #-}
union hm1 hm2 = case (size hm1, size hm2) of
  ((Ur sz1, hm1), (Ur sz2, hm2)) -> DataFlow.do
    (parent, child) <- if sz1 >= sz2 then (hm1, hm2) else (hm2, hm1)
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
  probeKeyForAlter k hm & \case
    (Ur (NotFound st), hm) ->
      -- not found!
      f Nothing Control.<&> \case
        Ur Nothing -> hm -- No modification needed
        Ur (Just !v) -> probeForInsert k v st hm
    -- Already inserted with older value.
    (Ur (Found loc), hm) ->
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
    go :: Int -> LUV.Vector IndexInfo %1 -> KVs k v %1 -> HashMap k v
    go !i !idcs !kvs =
      case LUV.unsafeGet ((i + 1) `rem` capa) idcs of
        (Ur ixi, idcs)
          | ixi.dib P.== 0 -> DataFlow.do
              -- Reaches the stop bucket: empty or DIB = 0.
              -- By invariants, all emtpy buckets MUST have DIB = 0,
              -- so we can just check dib of the next bucket.
              kvs <- LV.unsafeSet i Strict.Nothing kvs
              idcs <- LUV.unsafeSet i IndexInfo {residual = 0, dib = 0} idcs
              HashMap (size - 1) capa maxDIB idcs kvs
          | otherwise -> DataFlow.do
              -- Need to shift back
              kvs <- unsafeSwapBoxed i (i + 1) kvs
              idcs <- unsafeSwapUnboxed i (i + 1) idcs
              -- Decrement DIB
              idcs <- LUV.modify_ (#dib -~ 1) i idcs
              go ((i + 1) `rem` capa) idcs kvs

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
  (Hashable k) =>
  k -> v -> ProbeSuspended -> HashMap k v %1 -> HashMap k v
probeForInsert !k !v ProbeSuspended {..} (HashMap size capa maxDIB idcs kvs) =
  case endType of
    Vacant -> growToFit (size + 1) DataFlow.do
      idcs <- LUV.unsafeSet offset IndexInfo {residual = initialBucket, dib = dibAtMiss} idcs
      kvs <- LV.unsafeSet offset (Strict.Just (Entry k v)) kvs
      HashMap (size + 1) capa maxDIB idcs kvs
    Paused -> growToFit (size + 1) DataFlow.do
      go maxDIB IndexInfo {residual = initialBucket, dib = dibAtMiss} (Entry k v) offset idcs kvs
  where
    go ::
      DIB ->
      IndexInfo ->
      Entry k v ->
      Int ->
      LUV.Vector IndexInfo %1 ->
      KVs k v %1 ->
      HashMap k v
    go !curMaxDIB !newIdxInfo !newEntry !idx !idcs !kvs =
      LV.unsafeGet idx kvs & \case
        (Ur Strict.Nothing, kvs) ->
          -- Found a vacant spot
          DataFlow.do
            !idcs <- LUV.unsafeSet idx newIdxInfo idcs
            !kvs <- LV.unsafeSet idx (Strict.Just newEntry) kvs
            HashMap (size + 1) capa curMaxDIB idcs kvs
        (Ur (Strict.Just existingEntry), kvs) ->
          -- Occupied, need to compare DIBs
          LUV.unsafeGet idx idcs & \(Ur existingIdxInfo, idcs) ->
            if existingIdxInfo.dib P.< newIdxInfo.dib
              then DataFlow.do
                -- Takes from the rich and gives to the poor
                !idcs <- LUV.unsafeSet idx newIdxInfo idcs
                !kvs <- LV.unsafeSet idx (Strict.Just newEntry) kvs
                go
                  (P.max newIdxInfo.dib curMaxDIB)
                  (increment existingIdxInfo)
                  existingEntry
                  ((idx + 1) `rem` capa)
                  idcs
                  kvs
              else
                go
                  curMaxDIB
                  (increment newIdxInfo)
                  newEntry
                  ((idx + 1) `rem` capa)
                  idcs
                  kvs

increment :: IndexInfo -> IndexInfo
{-# INLINE increment #-}
increment = #dib +~ 1

lookup :: (Hashable k) => k -> HashMap k v %1 -> (Ur (Maybe v), HashMap k v)
lookup k hm =
  probeKeyForAlter k hm & \case
    (Ur (NotFound _), hm) -> (Ur Nothing, hm)
    (Ur (Found loc), hm) -> (Ur (Just loc.val), hm)

member :: (Hashable k) => k -> HashMap k v %1 -> (Ur Bool, HashMap k v)
member k hm =
  probeKeyForAlter k hm & \case
    (Ur NotFound {}, hm) -> (Ur False, hm)
    (Ur Found {}, hm) -> (Ur True, hm)

delete :: (Hashable k) => k -> HashMap k v %1 -> (Ur (Maybe v), HashMap k v)
{-# INLINE delete #-}
delete k =
  swapTuple
    . flip runState (Ur Nothing)
    . alterF (\old -> state \new -> (new, Ur old)) k

growToFit :: (Hashable k) => Int -> HashMap k v %1 -> HashMap k v
growToFit targetSize (HashMap size capa maxDIB idcs kvs) =
  let finalSize = 2 ^ ceiling @_ @Int (logBase 2 (fromIntegral targetSize / maxLoadFactor))
   in if fromIntegral targetSize / fromIntegral capa >= maxLoadFactor
        then resize finalSize (HashMap size capa maxDIB idcs kvs)
        else HashMap size capa maxDIB idcs kvs

data Location v = Location
  { foundAt :: !Int
  , indexInfo :: {-# UNPACK #-} !IndexInfo
  , val :: !v
  }
  deriving (Show)

data LookupResult v
  = Found (Location v)
  | NotFound ProbeSuspended

data ProbeSuspended = ProbeSuspended
  { initialBucket :: {-# UNPACK #-} !Int
  , offset :: {-# UNPACK #-} !Int
  , endType :: !EndType
  , dibAtMiss :: {-# UNPACK #-} !DIB
  }
  deriving (Show)

data EndType = Paused | Vacant
  deriving (Show, P.Eq, P.Ord, Generic)

probeKeyForAlter :: (Hashable k) => k -> HashMap k v %1 -> (Ur (LookupResult v), HashMap k v)
probeKeyForAlter k (HashMap size capa maxDIB idcs kvs) =
  go start 0 idcs kvs
  where
    !start = hash k `mod` capa
    go :: Int -> DIB -> LUV.Vector IndexInfo %1 -> KVs _ _ %1 -> (Ur (LookupResult _), HashMap _ _)
    go !idx !dib !idcs !kvs
      | dib P.> maxDIB =
          ( Ur $
              NotFound
                ProbeSuspended
                  { initialBucket = start
                  , offset = idx
                  , endType = Paused
                  , dibAtMiss = dib
                  }
          , HashMap size capa maxDIB idcs kvs
          )
      | otherwise =
          LV.unsafeGet idx kvs & \case
            (Ur Strict.Nothing, kvs) ->
              ( Ur $
                  NotFound
                    ProbeSuspended
                      { initialBucket = start
                      , offset = idx
                      , endType = Vacant
                      , dibAtMiss = dib
                      }
              , HashMap size capa maxDIB idcs kvs
              )
            (Ur (Strict.Just (Entry k' val)), kvs)
              | k P.== k' -> LUV.unsafeGet idx idcs & \(Ur indexInfo, idcs) -> (Ur $ Found Location {foundAt = idx, ..}, HashMap size capa maxDIB idcs kvs)
              | otherwise ->
                  case LUV.unsafeGet idx idcs of
                    (Ur existing, idcs)
                      | dib P.< existing.dib ->
                          ( Ur $
                              NotFound
                                ProbeSuspended
                                  { initialBucket = start
                                  , offset = idx
                                  , endType = Paused
                                  , dibAtMiss = dib
                                  }
                          , HashMap size capa maxDIB idcs kvs
                          )
                      | otherwise -> go ((idx + 1) `rem` capa) (dib + 1) idcs kvs

resize :: (Hashable k) => Int -> HashMap k v %1 -> HashMap k v
resize capa hm = DataFlow.do
  (lin, hm) <- withLinearly hm
  hm' <- new capa lin
  foldMapWithKey (curry $ Ur P.. FML.singleton) hm & \(Ur ents) ->
    flip execState hm' $ Control.fmap unur $ runUrT $ P.forM_ ents \(!k, !v) ->
      UrT $! Control.fmap move $! modify $! uncurry lseq . insert k v

toList :: HashMap k v %1 -> Ur [(k, v)]
{-# INLINE toList #-}
toList = Ur.lift DL.toList . foldMapWithKey (curry $ Ur P.. DL.singleton)

fromList :: (Hashable k) => [(k, v)] -> Linearly %1 -> HashMap k v
fromList kvs =
  appEndo
    ( P.foldMap'
        (\(!k, !v) -> Endo $ uncurry lseq . insert k v)
        kvs
    )
    . new (floor $ fromIntegral (P.length kvs) * maxLoadFactor)
