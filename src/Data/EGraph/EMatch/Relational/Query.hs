{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
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
  CompiledVar (..),
  PatternQuery (..),
  compile,
  findVars,
  substAtom,
  substRelation,
) where

import Control.Lens (preview)
import Control.Lens.Extras (is)
import Control.Monad.Trans.State.Strict (State, StateT (..), evalState, state)
import Data.Coerce (coerce)
import Data.DList qualified as DL
import Data.EGraph.Types
import Data.Foldable (Foldable (foldMap'))
import Data.Foldable qualified as F
import Data.Functor.Classes
import Data.Generics.Labels ()
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.Hashable.Lifted
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import GHC.Generics
import Text.Show.Deriving

data Relation l v = MkRel {id :: !v, args :: !(l v)}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

deriveShow1 ''Relation

deriving via Generically1 (Relation l) instance (Eq1 l) => Eq1 (Relation l)

deriving via Generically1 (Relation l) instance (Ord1 l) => Ord1 (Relation l)

deriving anyclass instance (Hashable1 l) => Hashable1 (Relation l)

data CompiledVar v = Fresh !Word | PVar v
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 CompiledVar

deriveShow1 ''CompiledVar

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
  = (:-) {head :: [v], body :: NonEmpty (Atom l v)}
  deriving (Show, Eq, Ord, Generic, Generic1, Functor, Foldable, Traversable)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 (ConjunctiveQuery l)

deriveShow1 ''ConjunctiveQuery
deriveShow1 ''Query

findVars :: (Eq v, Foldable l) => v -> Atom l v -> Maybe (NonEmpty Int)
findVars v (Atom pattern) =
  NE.nonEmpty $ List.elemIndices (QVar v) $ F.toList pattern

newtype FreshM a = FreshM (State Word a)
  deriving newtype (Functor, Applicative, Monad)

fresh :: FreshM (CompiledVar v)
fresh = FreshM $ do
  n <- state (\n -> (n, n + 1))
  pure $ Fresh n

runFreshM :: forall a. FreshM a -> a
runFreshM = coerce $ flip (evalState @Word @a) (0 :: Word)

data PatternQuery l v = PatternQuery
  { root :: !(CompiledVar v)
  , patQuery :: !(Query l (CompiledVar v))
  }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic, Generic1)
  deriving anyclass (Hashable, Hashable1)
  deriving (Eq1, Ord1) via Generically1 (PatternQuery l)

compile ::
  forall l v.
  (Hashable v, Traversable l) =>
  Pattern l v ->
  PatternQuery l v
compile = \case
  PNode ls
    | Just vars <- mapM (fmap PVar . preview #_Metavar) ls ->
        -- Not a nested query - no join required!
        let root = Fresh 0
         in PatternQuery {root, patQuery = Conj $ (root : F.toList vars) :- NE.singleton (Atom $ QVar <$> MkRel {id = root, args = vars})}
  pat0 ->
    let (root, atms) = runFreshM (aux pat0)
        vs = HashSet.toList $ foldMap' (HashSet.singleton . PVar) pat0
        patQuery = case NE.nonEmpty $ DL.toList atms of
          Nothing -> SelectAll root
          Just atms' -> Conj $ vs :- atms'
     in PatternQuery {..}
    where
      aux :: Pattern l v -> FreshM (CompiledVar v, DL.DList (Atom l (CompiledVar v)))
      aux (PNode l) = do
        v <- fresh
        vsatmss <- mapM aux l
        let atms =
              DL.cons (Atom (MkRel (QVar v) $ QVar . fst <$> vsatmss)) $
                foldMap' snd vsatmss
        pure (v, atms)
      aux (Metavar v) = pure (PVar v, mempty)

substAtom :: forall l v. (Functor l, Eq v) => v -> EClassId -> Atom l v -> Atom l v
substAtom = coerce $ substRelation @l @v

substRelation ::
  forall l v.
  (Functor l, Eq v) =>
  v -> EClassId -> Relation l (EClassIdOrVar v) -> Relation l (EClassIdOrVar v)
substRelation v eid (MkRel hd args) =
  let subs = \case QVar v' | v == v' -> EId eid; x -> x
   in MkRel (subs hd) (fmap subs args)
