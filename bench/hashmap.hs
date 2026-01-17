{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main (main) where

import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate)
import Control.Monad.Borrow.Pure (linearly)
import Data.HashMap.Mutable.Linear qualified as LB
import Data.HashMap.Mutable.Linear.Witness qualified as LB
import Data.HashMap.RobinHood.Mutable.Linear qualified as RH
import Data.Hashable (Hashable (..))
import Data.Linear.Witness.Compat (fromPB)
import GHC.Generics (Generic)
import Prelude.Linear (Ur (..), lseq, unur, (&))
import Prelude.Linear qualified as PL
import Test.Tasty.Bench

-- | Key with expensive equality but cheap hash.
-- Hash only uses the prefix (Int), but Eq compares the full payload.
data ExpensiveKey = ExpensiveKey
  { ekPrefix :: {-# UNPACK #-} !Int
  , ekPayload :: ![Int] -- expensive to compare
  }
  deriving (Show, Generic, NFData)

instance Eq ExpensiveKey where
  -- Force full payload comparison even if prefixes differ
  ExpensiveKey p1 payload1 == ExpensiveKey p2 payload2 =
    p1 == p2 && payload1 == payload2
  {-# INLINE (==) #-}

instance Hashable ExpensiveKey where
  -- Only hash the prefix - cheap!
  hashWithSalt s (ExpensiveKey p _) = hashWithSalt s p
  {-# INLINE hashWithSalt #-}

-- | Benchmark inserting N elements into an empty map
benchInsertRH :: (Hashable k) => [(k, v)] -> [(k, v)]
benchInsertRH kvs = unur PL.$ linearly \lin ->
  let %1 !hm = RH.new (length kvs) lin
   in RH.toList (RH.insertMany kvs hm)

benchInsertLB :: (Hashable k) => [(k, v)] -> [(k, v)]
benchInsertLB kvs = unur PL.$ LB.empty (length kvs) \hm ->
  LB.toList (insertManyLB kvs hm)

insertManyLB :: (Hashable k) => [(k, v)] -> LB.HashMap k v %1 -> LB.HashMap k v
insertManyLB [] hm = hm
insertManyLB ((k, v) : rest) hm = insertManyLB rest (LB.insert k v hm)

-- | Benchmark fromList
benchFromListRH :: (Hashable k) => [(k, v)] -> [(k, v)]
benchFromListRH kvs = unur PL.$ linearly \lin ->
  RH.toList (RH.fromList kvs lin)

-- | Benchmark fromList
benchFromListLB :: (Hashable k) => [(k, v)] -> [(k, v)]
benchFromListLB kvs = unur PL.$ linearly \lin ->
  LB.toList (LB.fromListL kvs PL.$ fromPB lin)

-- | Benchmark lookup after insert
benchLookupRH :: forall k v. (Hashable k) => [(k, v)] -> [k] -> Int
benchLookupRH kvs keys = unur PL.$ linearly \lin ->
  let %1 !hm = RH.insertMany kvs (RH.new (length kvs) lin)
   in go 0 keys hm
  where
    go :: Int -> [k] -> RH.HashMap k v %1 -> Ur Int
    go !acc [] hm = hm `lseq` Ur acc
    go !acc (k : ks) hm =
      RH.lookup k hm & \(Ur mv, hm') ->
        go (acc + maybe 0 (const 1) mv) ks hm'

benchLookupLB :: forall k v. (Hashable k) => [(k, v)] -> [k] -> Int
benchLookupLB kvs keys = unur PL.$ LB.empty (length kvs) \hm ->
  let %1 !hm' = insertManyLB kvs hm
   in goLB 0 keys hm'
  where
    goLB :: Int -> [k] -> LB.HashMap k v %1 -> Ur Int
    goLB !acc [] hm = hm `lseq` Ur acc
    goLB !acc (k : ks) hm =
      LB.lookup k hm & \(Ur mv, hm') ->
        goLB (acc + maybe 0 (const 1) mv) ks hm'

-- | Generate test data
mkTestData :: Int -> [(Int, Int)]
mkTestData n = [(i, i) | i <- [1 .. n]]

-- | Generate expensive key test data.
-- Keys have unique prefixes but large payloads (100 elements each).
-- This creates many hash collisions when prefixes collide mod capacity.
mkExpensiveTestData :: Int -> [(ExpensiveKey, Int)]
mkExpensiveTestData n =
  [ (ExpensiveKey i [i .. i + 99], i)
  | i <- [1 .. n]
  ]

-- | Generate expensive keys with hash collisions.
-- All keys have the same prefix (same hash) but different payloads.
-- This maximizes the benefit of fingerprint check since all slots
-- have the same hash, forcing full equality checks without fingerprint.
mkCollidingExpensiveTestData :: Int -> [(ExpensiveKey, Int)]
mkCollidingExpensiveTestData n =
  [ (ExpensiveKey 42 [i .. i + 99], i) -- all hash to same bucket!
  | i <- [1 .. n]
  ]

main :: IO ()
main = do
  let sizes = [100, 1000, 10000]
  let smallSizes = [100, 1000] -- colliding is expensive, use smaller sizes

  -- Pre-generate test data
  testData <- mapM (\n -> evaluate $ force $ mkTestData n) sizes
  expensiveData <- mapM (\n -> evaluate $ force $ mkExpensiveTestData n) sizes
  collidingData <- mapM (\n -> evaluate $ force $ mkCollidingExpensiveTestData n) smallSizes

  defaultMain
    [ bgroup "insert" $
        zipWith
          ( \n kvs ->
              bgroup
                (show n)
                [ bench "robin-hood" $ nf benchInsertRH kvs
                , bench "linear-base" $ nf benchInsertLB kvs
                ]
          )
          sizes
          testData
    , bgroup "fromList" $
        zipWith
          ( \n kvs ->
              bgroup
                (show n)
                [ bench "robin-hood" $ nf benchFromListRH kvs
                , bench "linear-base" $ nf benchFromListLB kvs
                ]
          )
          sizes
          testData
    , bgroup "lookup" $
        zipWith
          ( \n kvs ->
              let keys = map fst kvs
               in bgroup
                    (show n)
                    [ bench "robin-hood" $ nf (benchLookupRH kvs) keys
                    , bench "linear-base" $ nf (benchLookupLB kvs) keys
                    ]
          )
          sizes
          testData
    , bgroup "expensive-key-insert" $
        zipWith
          ( \n kvs ->
              bgroup
                (show n)
                [ bench "robin-hood" $ nf benchInsertRH kvs
                , bench "linear-base" $ nf benchInsertLB kvs
                ]
          )
          sizes
          expensiveData
    , bgroup "expensive-key-lookup" $
        zipWith
          ( \n kvs ->
              let keys = map fst kvs
               in bgroup
                    (show n)
                    [ bench "robin-hood" $ nf (benchLookupRH kvs) keys
                    , bench "linear-base" $ nf (benchLookupLB kvs) keys
                    ]
          )
          sizes
          expensiveData
    , bgroup "colliding-expensive-key-lookup" $
        zipWith
          ( \n kvs ->
              let keys = map fst kvs
               in bgroup
                    (show n)
                    [ bench "robin-hood" $ nf (benchLookupRH kvs) keys
                    , bench "linear-base" $ nf (benchLookupLB kvs) keys
                    ]
          )
          smallSizes
          collidingData
    ]
