{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Immutable (
  -- * Immutable EGraph
  EGraph (),
  Analysis (..),

  -- * Construction
  empty,
  new,
  fromList,

  -- * Conversion between mutable 'Raw.EGraph'.
  freeze,
  thaw,
  unsafeThaw,

  -- * Queries
  find,
  lookup,
  lookupEClass,
  canonicalize,
  equivalent,
  lookupTerm,
  ematch,
  buildDatabase,

  -- * In-place update
  modify,

  -- * Equality saturation
  saturate,
  SaturationConfig (..),
  SaturationError (..),
  HasDatabase,
  Language,
  Rule (..),
  (==>),
  named,

  -- * Extraction
  extractBest,
  extractBest_,
  extractBestOf,

  -- * Re-exports
  ENode (..),
  EClassId (..),
  Pattern (..),
  Term,
  wrapTerm,
  unwrapTerm,
) where

import Control.Functor.Linear (StateT (..), evalStateT)
import Control.Functor.Linear qualified as Control
import Control.Lens (Lens')
import Control.Monad.Borrow.Pure (BO, Linearly, Mut, Share, linearly, modifyLinearOnlyBO, modifyLinearOnlyBO_, sharing)
import Control.Monad.Borrow.Pure.Utils (unsafeLeak)
import Data.EGraph.EMatch.Relational qualified as Rel
import Data.EGraph.EMatch.Relational.Database (Database, HasDatabase)
import Data.EGraph.EMatch.Relational.Database qualified as RawDb
import Data.EGraph.EMatch.Types (Substitution)
import Data.EGraph.Saturation hiding (extractBest, extractBestOf, extractBest_, saturate)
import Data.EGraph.Saturation qualified as Raw
import Data.EGraph.Types (EClassId (..), ENode (..), unwrapTerm, wrapTerm)
import Data.EGraph.Types.EGraph (Analysis, Term)
import Data.EGraph.Types.EGraph qualified as Raw
import Data.EGraph.Types.Language (Language)
import Data.EGraph.Types.Pattern (Pattern (..))
import Data.Foldable (for_)
import Data.Functor.Classes (Show1)
import Data.Functor.Linear qualified as PL
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty (NonEmpty)
import Data.Unrestricted.Linear (Ur (..), dup, lseq, move, unur)
import Data.Unrestricted.Linear.Internal.UrT (UrT (..), runUrT)
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)
import GHC.Exts (Multiplicity (..))
import Prelude.Linear (Dupable, Movable)
import Prelude.Linear qualified as PL
import Text.Show.Borrowed (Display, displayPrec)
import Unsafe.Linear qualified as Unsafe
import Prelude as P hiding (lookup)

data EGraph d l where
  EG :: !(Raw.EGraph d l) %'Many -> EGraph d l

instance (Display d, Copyable1 l, Show1 l) => Show (EGraph d l) where
  showsPrec d = withRaw PL.$ displayPrec d

new ::
  (Hashable1 l, Movable1 l, Copyable1 l, Analysis l d, Movable a, Show1 l) =>
  (forall α. Mut α (Raw.EGraph d l) %1 -> BO α a) %1 ->
  Ur (EGraph d l, a)
{-# INLINE new #-}
new f = linearly \lin ->
  let %1 !(Ur a, eg) = modifyLinearOnlyBO (Raw.new lin) (Control.fmap move PL.. f)
      %1 !(Ur !frozen) = freeze eg
   in Ur (frozen, a)

modify ::
  (Hashable1 l, Movable1 l, Copyable1 l, Analysis l d, Show1 l) =>
  (forall α. Mut α (Raw.EGraph d l) %1 -> BO α ()) %1 ->
  EGraph d l ->
  Ur (EGraph d l)
{-# INLINE modify #-}
modify f egraph = linearly \lin ->
  let %1 !eg = modifyLinearOnlyBO_ (thaw egraph lin) f
   in freeze eg

empty :: (Hashable1 l) => EGraph d l
{-# INLINE empty #-}
empty = unur (linearly \l -> Unsafe.toLinear (Ur . EG) (Raw.new l))

fromList ::
  forall d l.
  (Analysis l d, Hashable1 l, Movable1 l, Show1 l) =>
  [Raw.Term l] -> EGraph d l
{-# INLINE fromList #-}
fromList terms = unur PL.$ linearly \l ->
  Unsafe.toLinear (Ur . EG) PL.$
    modifyLinearOnlyBO_ (Raw.new l) \egraph ->
      PL.flip evalStateT egraph PL.$ Control.fmap unur PL.$ runUrT do
        for_ terms \term ->
          UrT $ StateT \egraph -> Control.do
            (Ur _, Ur _, egraph) <- Raw.addTerm term egraph
            Control.pure (Ur (), egraph)

-- | _O(1)_. Freezes a mutable EGraph into an immutable one.
freeze ::
  (Hashable1 l, Movable1 l, Copyable1 l, Analysis l d, Show1 l) =>
  Raw.EGraph d l %1 -> Ur (EGraph d l)
{-# INLINE freeze #-}
freeze egraph =
  let %1 !eg = modifyLinearOnlyBO_ egraph (PL.void PL.. Raw.rebuild)
   in Unsafe.toLinear (Ur . EG) eg

-- | _O(n)_. Clones the immutable EGraph into a mutable one.
thaw :: (Movable1 l, Dupable d) => EGraph d l -> Linearly %1 -> Raw.EGraph d l
{-# INLINE thaw #-}
thaw egraph lin =
  let %1 !(!old, !new) = dup (unsafeThaw egraph lin)
   in unsafeLeak old `lseq` new

{- | _O(1)_. Unsafe helper to work with the raw EGraph inside an immutable EGraph.

NOTE: it is the caller's responsibility to ensure that the immutable EGraph
is not used after the 'unsafeThaw' is called.
-}
unsafeThaw ::
  EGraph d l ->
  Linearly %1 ->
  Raw.EGraph d l
{-# INLINE unsafeThaw #-}
unsafeThaw (EG !egraph) lin = lin `lseq` egraph

withRaw ::
  ( forall α.
    Share α (Raw.EGraph d l) -> BO α (Ur a)
  ) %1 ->
  EGraph d l ->
  a
{-# INLINE withRaw #-}
withRaw f (EG egraph) =
  let %1 !(Ur !a, eg) = modifyLinearOnlyBO egraph \egraph -> Control.do
        (r, egraph) <- sharing egraph f
        Control.pure (egraph `lseq` r)
   in unsafeLeak eg `lseq` a

find :: EClassId -> EGraph d l -> Maybe EClassId
{-# INLINE find #-}
find eid = withRaw (\egraph -> Raw.find egraph eid)

lookupEClass :: (Movable1 l) => EClassId -> EGraph d l -> Maybe (NonEmpty (ENode l))
{-# INLINE lookupEClass #-}
lookupEClass eid = withRaw (\egraph -> Raw.lookupEClass eid egraph)

canonicalize ::
  (Traversable l) =>
  ENode l -> EGraph d l -> Maybe (ENode l)
{-# INLINE canonicalize #-}
canonicalize node = withRaw (Raw.canonicalize node)

equivalent :: (Raw.Equatable l a) => EGraph d l -> a -> a -> Maybe Bool
{-# INLINE equivalent #-}
equivalent egraph a b = withRaw (\egraph -> Raw.equivalent egraph a b) egraph

lookup ::
  (Hashable1 l, Traversable l) =>
  ENode l -> EGraph d l -> Maybe EClassId
{-# INLINE lookup #-}
lookup node = withRaw (\egraph -> Raw.lookup node egraph)

lookupTerm ::
  forall d l.
  (Hashable1 l, Traversable l) =>
  Term l ->
  EGraph d l ->
  Maybe EClassId
{-# INLINE lookupTerm #-}
lookupTerm t = withRaw (Raw.lookupTerm t)

extractBest_ ::
  (Language l, CostModel cost l) =>
  EClassId ->
  EGraph (ExtractBest l cost) l ->
  Maybe (Term l, cost)
extractBest_ eid = withRaw (Raw.extractBest_ eid)

extractBest ::
  (Analysis l d, Language l, CostModel cost l) =>
  EClassId ->
  EGraph (ExtractBest l cost, d) l ->
  Maybe (Term l, cost)
extractBest eid = withRaw (Raw.extractBest eid)

extractBestOf ::
  (Analysis l d, Language l) =>
  Lens' d (ExtractBest l cost) ->
  EClassId ->
  EGraph d l ->
  Maybe (Term l, cost)
extractBestOf lens eid = withRaw (Raw.extractBestOf lens eid)

saturate ::
  (Language l, Show1 l, Hashable v, Show v, Analysis l d) =>
  SaturationConfig ->
  [Rule l v] ->
  EGraph d l ->
  Either (SaturationError l v) (EGraph d l)
saturate cfg rules = do
  case traverse compileRule rules of
    Left err -> const $ Left err
    Right rules ->
      Right . (\(Ur x) -> x) . modify \egraph ->
        Control.void PL.$ Raw.saturate cfg rules egraph

ematch ::
  (Language l, Show1 l, Hashable v, Show v) =>
  Pattern l v ->
  EGraph d l ->
  [(EClassId, Substitution v)]
ematch pat = withRaw PL.$ Rel.ematch pat

buildDatabase ::
  (HasDatabase l, Movable1 l, Traversable l) =>
  EGraph d l ->
  Database l
buildDatabase = withRaw RawDb.buildDatabase
