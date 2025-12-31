{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.Immutable (
  -- * Immutable EGraph
  EGraph (),

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
import Control.Monad.Borrow.Pure (BO, Linearly, Mut, Share, linearly, modifyLinearOnlyBO, modifyLinearOnlyBO_, sharing)
import Control.Monad.Borrow.Pure.Utils (unsafeLeak)
import Control.Monad.Trans.Maybe (MaybeT (..))
import Data.EGraph.EMatch.Relational.Database (HasDatabase)
import Data.EGraph.Saturation hiding (saturate)
import Data.EGraph.Saturation qualified as Raw
import Data.EGraph.Types (EClassId (..), ENode (..), Language, unwrapTerm, wrapTerm)
import Data.EGraph.Types.EGraph (Term)
import Data.EGraph.Types.EGraph qualified as Raw
import Data.EGraph.Types.Pattern (Pattern (..))
import Data.Fix (foldFixM)
import Data.Foldable (for_)
import Data.Functor.Linear qualified as PL
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import Data.List.NonEmpty (NonEmpty)
import Data.Unrestricted.Linear (Ur (..), dup, lseq, move, unur)
import Data.Unrestricted.Linear.Internal.UrT (UrT (..), runUrT)
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)
import GHC.Exts (Multiplicity (..))
import Prelude.Linear (Movable)
import Prelude.Linear qualified as PL
import Unsafe.Linear qualified as Unsafe
import Prelude as P hiding (lookup)

data EGraph l where
  EG :: !(Raw.EGraph l) %'Many -> EGraph l

new ::
  (Hashable1 l, Movable1 l, Copyable1 l, Traversable l, Movable a) =>
  (forall α. Mut α (Raw.EGraph l) %1 -> BO α a) %1 ->
  Ur (EGraph l, a)
{-# INLINE new #-}
new f = linearly \lin ->
  let %1 !(Ur a, eg) = modifyLinearOnlyBO (Raw.new lin) (Control.fmap move PL.. f)
      %1 !(Ur !frozen) = freeze eg
   in Ur (frozen, a)

modify ::
  (Hashable1 l, Movable1 l, Copyable1 l, Traversable l) =>
  (forall α. Mut α (Raw.EGraph l) %1 -> BO α ()) %1 ->
  EGraph l ->
  Ur (EGraph l)
{-# INLINE modify #-}
modify f egraph = linearly \lin ->
  let %1 !eg = modifyLinearOnlyBO_ (thaw egraph lin) f
   in freeze eg

empty :: (Hashable1 l) => EGraph l
{-# INLINE empty #-}
empty = unur (linearly \l -> Unsafe.toLinear (Ur . EG) (Raw.new l))

fromList :: (Hashable1 l, Traversable l, Movable1 l) => [Raw.Term l] -> EGraph l
{-# INLINE fromList #-}
fromList terms = unur PL.$ linearly \l ->
  Unsafe.toLinear (Ur . EG)
    PL.$ modifyLinearOnlyBO_ (Raw.new l) \egraph ->
      PL.flip evalStateT egraph PL.$ Control.fmap unur PL.$ runUrT do
        for_ terms \term ->
          UrT $ StateT \egraph -> Control.do
            (Ur _, Ur _, egraph) <- Raw.addTerm egraph term
            Control.pure (Ur (), egraph)

-- | _O(1)_. Freezes a mutable EGraph into an immutable one.
freeze ::
  (Hashable1 l, Movable1 l, Copyable1 l, Traversable l) =>
  Raw.EGraph l %1 -> Ur (EGraph l)
{-# INLINE freeze #-}
freeze egraph =
  let %1 !eg = modifyLinearOnlyBO_ egraph (PL.void PL.. Raw.rebuild)
   in Unsafe.toLinear (Ur . EG) eg

-- | _O(n)_. Clones the immutable EGraph into a mutable one.
thaw :: (Movable1 l) => EGraph l -> Linearly %1 -> Raw.EGraph l
{-# INLINE thaw #-}
thaw egraph lin =
  let %1 !(!old, !new) = dup (unsafeThaw egraph lin)
   in unsafeLeak old `lseq` new

{- | _O(1)_. Unsafe helper to work with the raw EGraph inside an immutable EGraph.

NOTE: it is the caller's responsibility to ensure that the immutable EGraph
is not used after the 'unsafeThaw' is called.
-}
unsafeThaw ::
  EGraph l ->
  Linearly %1 ->
  Raw.EGraph l
{-# INLINE unsafeThaw #-}
unsafeThaw (EG !egraph) lin = lin `lseq` egraph

withRaw ::
  ( forall α.
    Share α (Raw.EGraph l) -> BO α (Ur a)
  ) %1 ->
  EGraph l ->
  a
{-# INLINE withRaw #-}
withRaw f (EG egraph) =
  let %1 !(Ur !a, eg) = modifyLinearOnlyBO egraph \egraph -> Control.do
        (r, egraph) <- sharing egraph \egraph -> f egraph
        Control.pure (egraph `lseq` r)
   in unsafeLeak eg `lseq` a

find :: EClassId -> EGraph l -> Maybe EClassId
{-# INLINE find #-}
find eid = withRaw (\egraph -> Raw.find egraph eid)

lookupEClass :: (Movable1 l) => EClassId -> EGraph l -> Maybe (NonEmpty (ENode l))
{-# INLINE lookupEClass #-}
lookupEClass eid = withRaw (\egraph -> Raw.lookupEClass eid egraph)

canonicalize ::
  (Traversable l) =>
  ENode l -> EGraph l -> Maybe (ENode l)
{-# INLINE canonicalize #-}
canonicalize node = withRaw (\egraph -> Raw.canonicalize egraph node)

equivalent :: (Raw.Equatable l a) => EGraph l -> a -> a -> Maybe Bool
{-# INLINE equivalent #-}
equivalent egraph a b = withRaw (\egraph -> Raw.equivalent egraph a b) egraph

lookup ::
  (Hashable1 l, Traversable l) =>
  ENode l -> EGraph l -> Maybe EClassId
{-# INLINE lookup #-}
lookup node = withRaw (\egraph -> Raw.lookup node egraph)

lookupTerm ::
  forall l.
  (Hashable1 l, Traversable l) =>
  Term l ->
  EGraph l ->
  Maybe EClassId
{-# INLINE lookupTerm #-}
lookupTerm t =
  withRaw
    ( \egraph -> Control.do
        let go term =
              foldFixM
                (\t -> MaybeT $ UrT (Raw.lookup (ENode t) egraph))
                term
        runUrT PL.$ runMaybeT P.$ go t
    )

saturate ::
  (Hashable v, Language l, HasDatabase l) =>
  SaturationConfig ->
  [Rule l v] ->
  EGraph l ->
  Either (SaturationError l v) (EGraph l)
saturate cfg rules = do
  case traverse compileRule rules of
    Left err -> const $ Left err
    Right rules ->
      Right . (\(Ur x) -> x) . modify \egraph ->
        Control.void PL.$ Raw.saturate cfg rules egraph
