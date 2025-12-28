{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoFieldSelectors #-}

module Data.EGraph.EMatch.Relational.Query (
  Relation (..),
  Query (..),
  Atom (..),
  ConjunctiveQuery (..),
  EClassIdOrVar (..),
  CompiledVar (..),
  compile,
  findVars,
) where

import Control.Monad.Trans.State.Strict (State, StateT (..), evalState, state)
import Data.Coerce (coerce)
import Data.DList qualified as DL
import Data.EGraph.Types
import Data.Foldable (Foldable (foldMap'))
import Data.Foldable qualified as F
import Data.Functor.Classes
import Data.HashSet qualified as HashSet
import Data.Hashable
import Data.Hashable.Lifted
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (mapMaybe)
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
  = EClassId !EClassId
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
  NE.nonEmpty
    $ mapMaybe
      ( uncurry \cases
          !i (QVar v') | v == v' -> Just i
          _ _ -> Nothing
      )
    $ zip [0 ..]
    $ F.toList pattern

newtype FreshM a = FreshM (State Word a)
  deriving newtype (Functor, Applicative, Monad)

fresh :: FreshM (CompiledVar v)
fresh = FreshM $ do
  n <- state (\n -> (n, n + 1))
  pure $ Fresh n

runFreshM :: forall a. FreshM a -> a
runFreshM = coerce $ flip (evalState @Word @a) (0 :: Word)

compile ::
  forall l v.
  (Hashable v, Traversable l) =>
  Pattern l v -> Query l (CompiledVar v)
compile = \pat0 ->
  let (root, atms) = runFreshM (aux pat0)
      vs = HashSet.toList $ foldMap' (HashSet.singleton . PVar) pat0
   in case NE.nonEmpty $ DL.toList atms of
        Nothing -> SelectAll root
        Just atms' -> Conj $ vs :- atms'
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