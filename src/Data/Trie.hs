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

import Data.Bifunctor qualified as Bi
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
newtype Trie = Trie {branches :: HashMap EClassId Trie}
  deriving (Eq, Ord, Generic)

instance Show Trie where
  showsPrec d trie =
    showParen (d > 10) $
      showString "fromRows " . shows (toRows trie)

type Row = [EClassId]

toRows :: Trie -> [Row]
toRows = FML.toList . go
  where
    go (Trie hm)
      | HM.null hm = FML.singleton []
      | otherwise =
          foldMap'
            ( \(i, t) ->
                fmap (i :) (go t)
            )
            (HM.toList hm)
{-# INLINE toRows #-}

empty :: Trie
empty = Trie HM.empty
{-# INLINE empty #-}

member :: [EClassId] -> Trie -> Bool
member [] _ = True
member (i : is) (Trie vec) =
  if HM.member i vec
    then member is $ vec HM.! i
    else False
{-# INLINE member #-}

singleton :: [EClassId] -> Trie
singleton [] = Trie HM.empty
singleton (i : is) = Trie $ HM.singleton i (singleton is)
{-# INLINE singleton #-}

insert :: [EClassId] -> Trie -> Trie
insert [] trie = trie
insert (i : is) (Trie vec) =
  Trie $ HM.alter (Just . maybe (singleton is) (insert is)) i vec
{-# INLINE insert #-}

focus :: [Maybe EClassId] -> Trie -> Trie
focus [] trie = trie
focus (Nothing : xs) (Trie vec) = Trie $ focus xs <$> vec
focus (Just i : xs) (Trie vec) =
  if HM.member i vec
    then Trie (HM.singleton i $ focus xs $ vec HM.! i)
    else empty
{-# INLINE focus #-}

project :: NonEmpty Int -> Trie -> HashSet EClassId
project indices =
  Strict.fromJust
    . go 0 (IntSet.toAscList $ IntSet.fromList $ F.toList indices) Strict.Nothing
    . FML.singleton
  where
    go :: Int -> [Int] -> Strict.Maybe (HashSet EClassId) -> FMList Trie -> Strict.Maybe (HashSet EClassId)
    go !_ [] !acc _ = acc
    go !n (i : is) !acc tries
      | n == i =
          let (keys, chs) =
                foldMap'
                  (Bi.bimap HashSet.fromList FML.fromList . unzip . HM.toList . (.branches))
                  tries
              !acc' =
                Strict.Just $
                  Strict.maybe keys (HashSet.intersection keys) acc
           in go (n + 1) is acc' chs
      | otherwise =
          go (n + 1) (i : is) acc $!
            foldMap' (FML.fromList . F.toList . (.branches)) tries

cons :: EClassId -> Trie -> Trie
{-# INLINE cons #-}
cons i = Trie . HM.singleton i
