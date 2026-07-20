{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Data.Trie (
  Trie (),
  size,
  rootKeys,
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
  toKey,
  fromKey,
) where

import Control.Lens hiding (cons, indices)
import Control.Monad ((<$!>))
import Data.DList qualified as DL
import Data.EGraph.EMatch.Relational.Query
import Data.EGraph.Types.EClassId (EClassId)
import Data.FMList qualified as FML
import Data.Foldable (foldMap')
import Data.Foldable qualified as F
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (Alt (Alt))
import GHC.Generics

-- | E-class ids are 'Word' newtypes; rows are indexed by their 'Int' image.
toKey :: EClassId -> IM.Key
{-# INLINE toKey #-}
toKey = fromIntegral

fromKey :: IM.Key -> EClassId
{-# INLINE fromKey #-}
fromKey = fromIntegral

{- | A relation trie. Every level caches its key-set ('keys'), so projecting
the domain of a variable at this level is O(1) (cf. hegg's @tkeys@ — "quite
important for performance!").

Invariant: @keys == IM.keysSet branches@.
-}
data Trie = Trie
  { size :: {-# UNPACK #-} !Word
  , keys :: !IntSet
  , branches :: !(IntMap Trie)
  }
  deriving (Eq, Ord, Generic)

size :: Trie -> Word
size = (.size)

{-# INLINE rootKeys #-}
rootKeys :: Trie -> IntSet
rootKeys = (.keys)

instance Show Trie where
  showsPrec d trie =
    showParen (d > 10) $
      showString "fromRows " . shows (toRows trie)

type Row = [EClassId]

toRows :: Trie -> [Row]
toRows = FML.toList . go
  where
    go (Trie _ _ hm)
      | IM.null hm = FML.singleton []
      | otherwise =
          foldMap'
            ( \(i, t) ->
                fmap (fromKey i :) (go t)
            )
            (IM.toList hm)
{-# INLINE toRows #-}

empty :: Trie
empty = Trie 0 IS.empty IM.empty
{-# INLINE empty #-}

member :: [EClassId] -> Trie -> Bool
member [] _ = True
member (i : is) (Trie _ _ vec) =
  maybe False (member is) (IM.lookup (toKey i) vec)
{-# INLINE member #-}

singleton :: [EClassId] -> Trie
singleton [] = Trie 0 IS.empty IM.empty
singleton (i : is) = Trie 1 (IS.singleton (toKey i)) $ IM.singleton (toKey i) (singleton is)
{-# INLINE singleton #-}

insert :: [EClassId] -> Trie -> Trie
insert [] trie = trie
insert (i : is) (Trie n ks vec) =
  Trie (n + 1) (IS.insert (toKey i) ks) $
    IM.alter (Just . maybe (singleton is) (insert is)) (toKey i) vec
{-# INLINE insert #-}

{- | Focus the trie on the given indices.
__Invariant__: The indices in the first coordinate MUST be sorted in strictly ascending order.
-}
focus :: NonEmpty (Int, EClassId) -> Trie -> Trie
focus = fmap (fromMaybe empty) . go 0 . NE.toList
  where
    wrapTrie n = \hm ->
      if IM.null hm
        then Nothing
        else Just $ Trie n (IM.keysSet hm) hm
    go :: Int -> [(Int, EClassId)] -> Trie -> Maybe Trie
    go !_ [] trie = Just trie
    go !i kks@((k, eid) : ks) (Trie n _ vec)
      | i < k = wrapTrie n $ IM.mapMaybe (go (i + 1) kks) vec
      | otherwise =
          fmap (\t -> Trie t.size (IS.singleton (toKey eid)) $ IM.singleton (toKey eid) t) . go (i + 1) ks
            =<< IM.lookup (toKey eid) vec
{-# INLINE focus #-}

-- | Domain of a variable occurring at the given column positions.
project :: NonEmpty Int -> Trie -> IntSet
project indices =
  probe 0 (NE.fromList $ IS.toAscList $ IS.fromList $ F.toList indices)
  where
    probe :: Int -> NonEmpty Int -> Trie -> IntSet
    probe !n (i :| is) trie
      | n == i = case is of
          -- Fast path: the variable occurs only at this column; its domain
          -- is exactly this level's cached key-set.
          [] -> trie.keys
          i' : is' ->
            IS.fromList $
              mapMaybe
                (\(eid, t) -> go (n + 1) (i' :| is') eid t)
                (IM.toList trie.branches)
      | otherwise = foldMap' (probe (n + 1) (i :| is)) trie.branches
    go :: Int -> NonEmpty Int -> IM.Key -> Trie -> Maybe IM.Key
    go !n (i :| is) !eid !trie
      | n == i = do
          trie' <- IM.lookup eid trie.branches
          case is of
            [] -> pure eid
            i' : is' -> go (n + 1) (i' :| is') eid trie'
      | otherwise =
          alaf Alt foldMap (go (n + 1) (i :| is) eid) trie.branches

cons :: EClassId -> Trie -> Trie
{-# INLINE cons #-}
cons i t = Trie t.size (IS.singleton (toKey i)) (IM.singleton (toKey i) t)

fromRows :: [Row] -> Trie
fromRows = go
  where
    go [] = empty
    go ([] : _) = empty
    go rows =
      let dic =
            -- NB: group with DList values — (<>) on lists inside
            -- fromListWith would left-nest (++) and go quadratic per key.
            IM.map (go . DL.toList) $
              IM.fromListWith
                (flip (<>))
                [(toKey x, DL.singleton xs) | x : xs <- rows]
          -- NB: faithful to the previous implementation, sizes bottom out at
          -- 0 for leaf levels, so a database built via 'fromRows' reports
          -- size 0 throughout. Kept as-is to preserve the variable-ordering
          -- heuristic's observed behaviour; see TUNE-PLAN.
          !sz = sum (fmap (.size) dic)
       in Trie sz (IM.keysSet dic) dic

match :: [EClassIdOrVar VarId] -> Trie -> [IntMap EClassId]
match = go IM.empty
  where
    go !sub [] _ = [sub]
    go !sub (x : xs) (Trie _ _ hm) = case x of
      EId eid -> fromMaybe [] $ go sub xs <$!> IM.lookup (toKey eid) hm
      QVar v ->
        foldMap
          ( \(eid, trie') ->
              case IM.lookup v sub of
                Nothing -> go (IM.insert v (fromKey eid) sub) xs trie'
                Just eid'
                  | fromKey eid == eid' -> go sub xs trie'
                  | otherwise -> []
          )
          (IM.toList hm)
