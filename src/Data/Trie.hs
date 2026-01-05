{-# LANGUAGE OverloadedRecordDot #-}

module Data.Trie (
  Trie (),
  empty,
  toRows,
  fromRows,
  cons,
  member,
  singleton,
  insert,
  focus,
  project,
  match,
) where

import Control.Foldl qualified as L
import Control.Lens hiding (cons, indices)
import Control.Monad ((<$!>))
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.EMatch.Types (Substitution, insertVar, lookupVar)
import Data.EGraph.Types.EClassId (EClassId)
import Data.FMList qualified as FML
import Data.Foldable (foldMap')
import Data.Foldable qualified as F
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable (Hashable)
import Data.IntSet qualified as IntSet
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (Alt (Alt))
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

{- | Focus the trie on the given indices.
__Invariant__: The indices in the first coordinate MUST be sorted in strictly ascending order.
-}
focus :: NonEmpty (Int, EClassId) -> Trie -> Trie
focus = fmap (fromMaybe empty) . go 0 . NE.toList
  where
    wrapTrie = \hm ->
      if HM.null hm
        then Nothing
        else Just $ Trie hm
    go :: Int -> [(Int, EClassId)] -> Trie -> Maybe Trie
    go !_ [] trie = Just trie
    go !i kks@((k, eid) : ks) (Trie vec)
      | i < k = wrapTrie $ HM.mapMaybe (go (i + 1) kks) vec
      | otherwise =
          fmap (Trie . HM.singleton eid) . go (i + 1) ks =<< HM.lookup eid vec
{-# INLINE focus #-}

project :: NonEmpty Int -> Trie -> HashSet EClassId
project indices =
  HashSet.fromList
    . probe 0 (NE.fromList $ IntSet.toAscList $ IntSet.fromList $ F.toList indices)
  where
    probe :: Int -> NonEmpty Int -> Trie -> [EClassId]
    probe !n (i :| is) trie
      | n == i = mapMaybe (uncurry $ go (n + 1) is) $ HM.toList trie.branches
      | otherwise = foldMap' (probe (n + 1) (i :| is)) trie.branches
    go :: Int -> [Int] -> EClassId -> Trie -> Maybe EClassId
    go !_ [] !eid _ = pure eid
    go !n (i : is) !eid !trie
      | n == i = do
          trie' <- HM.lookup eid trie.branches
          go (n + 1) is eid trie'
      | otherwise =
          alaf Alt foldMap (go (n + 1) (i : is) eid) trie.branches

cons :: EClassId -> Trie -> Trie
{-# INLINE cons #-}
cons i = Trie . HM.singleton i

fromRows :: [Row] -> Trie
fromRows = go
  where
    go [] = Trie HM.empty
    go ([] : _) = Trie HM.empty
    go rows =
      L.fold (L.premap uncons $ L.handles _Just $ Trie <$> L.foldByKeyHashMap (go <$> L.list)) rows

match :: (Hashable v) => [EClassIdOrVar v] -> Trie -> [Substitution v]
match = go mempty
  where
    go !sub [] _ = [sub]
    go !sub (x : xs) (Trie hm) = case x of
      EId eid -> fromMaybe [] $ go sub xs <$!> HM.lookup eid hm
      QVar v ->
        foldMap
          ( \(eid, trie') ->
              case lookupVar v sub of
                Nothing -> go (insertVar v eid sub) xs trie'
                Just eid'
                  | eid == eid' -> go sub xs trie'
                  | otherwise -> []
          )
          (HM.toList hm)
