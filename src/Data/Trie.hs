{-# LANGUAGE OverloadedRecordDot #-}

module Data.Trie (
  Trie (),
  empty,
  toRows,
  cons,
  member,
  singleton,
  insert,
  focus,
  project,
) where

import Control.Arrow ((&&&))
import Data.EGraph.Types.EClassId (EClassId)
import Data.FMList (FMList)
import Data.FMList qualified as FML
import Data.Foldable (foldMap')
import Data.Foldable qualified as F
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.IntSet qualified as IntSet
import Data.List.NonEmpty (NonEmpty)
import Data.Strict.Maybe qualified as Strict
import GHC.Generics

-- Invariant: keys are subset of branches's keys
data Trie = Trie
  { keys :: {-# UNPACK #-} !(HashSet EClassId)
  , branches :: {-# UNPACK #-} !(HashMap EClassId Trie)
  }
  deriving (Eq, Ord, Generic)

instance Show Trie where
  showsPrec d trie =
    showParen (d > 10) $
      showString "fromRows " . shows (toRows trie)

type Row = [EClassId]

toRows :: Trie -> [Row]
toRows = FML.toList . go
  where
    go (Trie _ hm)
      | HM.null hm = FML.singleton []
      | otherwise =
          foldMap'
            ( \(i, t) ->
                fmap (i :) (go t)
            )
            (HM.toList hm)
{-# INLINE toRows #-}

empty :: Trie
empty = Trie mempty HM.empty
{-# INLINE empty #-}

member :: [EClassId] -> Trie -> Bool
member [] _ = True
member (i : is) (Trie keys vec) =
  if HashSet.member i keys
    then member is $ vec HM.! i
    else False
{-# INLINE member #-}

singleton :: [EClassId] -> Trie
singleton [] = Trie mempty HM.empty
singleton (i : is) = Trie (HashSet.singleton i) $ HM.singleton i (singleton is)
{-# INLINE singleton #-}

insert :: [EClassId] -> Trie -> Trie
insert [] trie = trie
insert (i : is) (Trie keys vec) =
  Trie (HashSet.insert i keys) $ HM.alter (Just . maybe (singleton is) (insert is)) i vec
{-# INLINE insert #-}

focus :: [Maybe EClassId] -> Trie -> Trie
focus [] trie = trie
focus (Nothing : xs) (Trie keys trie) = Trie keys $ focus xs <$> trie
focus (Just i : xs) (Trie keys trie) =
  if HashSet.member i keys
    then Trie (HashSet.singleton i) $ HM.singleton i $ focus xs $ trie HM.! i
    else empty
{-# INLINE focus #-}

project :: NonEmpty Int -> Trie -> HashSet EClassId
project indices =
  Strict.fromJust
    . go 0 (IntSet.toAscList $ IntSet.fromList $ F.toList indices) Strict.Nothing
    . pure
  where
    go :: Int -> [Int] -> Strict.Maybe (HashSet EClassId) -> FMList Trie -> Strict.Maybe (HashSet EClassId)
    go !_ [] !acc _ = acc
    go !n (i : is) !acc tries
      | n == i =
          let (keys, chs) = foldMap' ((.keys) &&& (FML.fromList . F.toList . (.branches))) tries
              !acc' =
                Strict.Just $
                  Strict.maybe keys (HashSet.intersection keys) acc
           in go (n + 1) is acc' chs
      | otherwise =
          go (n + 1) (i : is) acc $!
            foldMap' (FML.fromList . F.toList . (.branches)) tries

cons :: EClassId -> Trie -> Trie
{-# INLINE cons #-}
cons i = Trie (HashSet.singleton i) . HM.singleton i
