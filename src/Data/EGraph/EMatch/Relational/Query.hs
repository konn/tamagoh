{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoFieldSelectors #-}

module Data.EGraph.EMatch.Relational.Query (
  Relation (..),
  Query (..),
  Atom (..),
  ConjunctiveQuery (..),
  EClassIdOrVar (..),
  VarId,
  PatternQuery (..),
  compile,
  findVars,
  substAtom,
  substRelation,
) where

import Control.Lens (preview)
import Control.Monad.Trans.State.Strict (State, runState, state)
import Data.Coerce (coerce)
import Data.DList qualified as DL
import Data.EGraph.Types
import Data.Foldable qualified as F
import Data.Functor.Classes
import Data.Generics.Labels ()
import Data.HashMap.Strict qualified as HM
import Data.Hashable
import Data.Hashable.Lifted
import Data.IntMap.Strict qualified as IM
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Vector qualified as V
import GHC.Generics
import Text.Show.Deriving

data Relation l v = MkRel {id :: !v, args :: !(l v)}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

deriveShow1 ''Relation

deriving via Generically1 (Relation l) instance (Eq1 l) => Eq1 (Relation l)

deriving via Generically1 (Relation l) instance (Ord1 l) => Ord1 (Relation l)

deriving anyclass instance (Hashable1 l) => Hashable1 (Relation l)

{- | An interned pattern variable: both user metavariables and internal
(fresh) variables are compiled to dense indices @0 .. n-1@, so all
query-internal maps can key on 'Int' ('Data.IntMap.IntMap' \/
'Data.IntSet.IntSet') with no hashing of user variables in the join's
inner loop.
-}
type VarId = Int

data EClassIdOrVar v
  = EId !EClassId
  | QVar !v
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 EClassIdOrVar

deriveShow1 ''EClassIdOrVar

newtype Atom l v = Atom (Relation l (EClassIdOrVar v))
  deriving (Generic, Generic1, Functor, Foldable, Traversable)
  deriving (Eq1, Ord1) via Generically1 (Atom l)

deriving stock instance (Show1 l, Show v) => Show (Atom l v)

deriving stock instance (Eq1 l, Eq v) => Eq (Atom l v)

deriving stock instance (Ord1 l, Ord v) => Ord (Atom l v)

deriving anyclass instance (Hashable1 l, Hashable v) => Hashable (Atom l v)

deriving anyclass instance (Hashable1 l, Functor l) => Hashable1 (Atom l)

deriveShow1 ''Atom

data Query l v
  = SelectAll v
  | Conj (ConjunctiveQuery l v)
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 (Query l)

data ConjunctiveQuery l v
  = (::-) {head :: [v], body :: NonEmpty (Atom l v)}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 (ConjunctiveQuery l)

deriveShow1 ''ConjunctiveQuery
deriveShow1 ''Query

findVars :: (Eq v, Foldable l) => v -> Atom l v -> Maybe (NonEmpty Int)
findVars v (Atom pattern) =
  NE.nonEmpty $ List.elemIndices (QVar v) $ F.toList pattern

-- | Interning state: dense ids for both fresh and user variables.
data InternState v = InternState
  { next :: !Int
  , seen :: !(HM.HashMap v VarId)
  , names :: [Maybe v]
  -- ^ Reversed list of variable names; 'Nothing' = internal (fresh) variable.
  }

type InternM v = State (InternState v)

freshVar :: InternM v VarId
freshVar = state \s -> (s.next, s {next = s.next + 1, names = Nothing : s.names})

internVar :: (Hashable v) => v -> InternM v VarId
internVar v = state \s -> case HM.lookup v s.seen of
  Just i -> (i, s)
  Nothing ->
    ( s.next
    , s {next = s.next + 1, seen = HM.insert v s.next s.seen, names = Just v : s.names}
    )

{- | Run interning, then renumber so that internal (fresh) variables occupy
ids @0..k-1@ and user metavariables @k..n-1@, each group in creation order.
The join's variable ordering breaks weight ties by ascending id, so internal
join variables (the structural join keys, root first) are eliminated before
user metavariables — a deterministic tie-break independent of user-chosen
variable names. (The pre-interning code broke ties by hash-map iteration
order through a pairing heap, i.e. arbitrarily.)
-}
runInternM :: InternM v a -> (a, VarId -> VarId, V.Vector (Maybe v))
runInternM act =
  let (a, s) = runState act (InternState 0 HM.empty [])
      names0 = V.fromList (reverse s.names)
      idx = zip [0 :: VarId ..] (V.toList names0)
      order = [i | (i, Nothing) <- idx] <> [i | (i, Just _) <- idx]
      tbl = IM.fromList (zip order [0 ..])
      remap old = tbl IM.! old
      names' = V.fromList (map (names0 V.!) order)
   in (a, remap, names')

data PatternQuery l v = PatternQuery
  { root :: !VarId
  , varNames :: !(V.Vector (Maybe v))
  -- ^ Indexed by 'VarId'; 'Just' for user metavariables.
  , patQuery :: !(Query l VarId)
  }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

compile ::
  forall l v.
  (Hashable v, Traversable l) =>
  Pattern l v ->
  PatternQuery l v
compile = \case
  PNode ls
    | Just vars <- mapM (preview #_Metavar) ls ->
        -- Not a nested query - no join required!
        let ((root0, args0), remap, varNames) = runInternM do
              r <- freshVar
              as <- traverse internVar vars
              pure (r, as)
            root = remap root0
            args = remap <$> args0
            hd = userVars varNames
         in PatternQuery
              { root
              , varNames
              , patQuery = Conj $ hd ::- NE.singleton (Atom $ QVar <$> MkRel {id = root, args})
              }
  pat0 ->
    let ((root0, atms0), remap, varNames) = runInternM (aux pat0)
        root = remap root0
        hd = userVars varNames
        patQuery = case NE.nonEmpty $ map (fmap remap) $ DL.toList atms0 of
          Nothing -> SelectAll root
          Just atms' -> Conj $ hd ::- atms'
     in PatternQuery {..}
    where
      aux :: Pattern l v -> InternM v (VarId, DL.DList (Atom l VarId))
      aux (PNode l) = do
        v <- freshVar
        vsatmss <- mapM aux l
        let atms =
              DL.cons (Atom (MkRel (QVar v) $ QVar . fst <$> vsatmss)) $
                F.foldMap' snd vsatmss
        pure (v, atms)
      aux (Metavar v) = (,mempty) <$> internVar v

-- | Ids of the user metavariables, in ascending order.
userVars :: V.Vector (Maybe v) -> [VarId]
userVars = V.ifoldr (\i mv acc -> maybe acc (const (i : acc)) mv) []

substAtom :: forall l v. (Functor l, Eq v) => v -> EClassId -> Atom l v -> Atom l v
substAtom = coerce $ substRelation @l @v

substRelation ::
  forall l v.
  (Functor l, Eq v) =>
  v -> EClassId -> Relation l (EClassIdOrVar v) -> Relation l (EClassIdOrVar v)
substRelation v eid (MkRel hd args) =
  let subs = \case QVar v' | v == v' -> EId eid; x -> x
   in MkRel (subs hd) (fmap subs args)
