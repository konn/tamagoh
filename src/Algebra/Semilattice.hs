{-# LANGUAGE DerivingStrategies #-}

module Algebra.Semilattice (Semilattice (..), WrapOrd (..)) where

import Data.Coerce (coerce)
import Data.Semigroup (Max, Min)

{- | (Unbounded) meet-semilattice.

Laws:

   * Associativity: @a '/\' (b '/\' c) = (a '/\' b) '/\' c@
   * Commutativity: @a '/\' b = b '/\' a@
   * Idempotency: @a '/\' a = a@
-}
class (Eq l) => Semilattice l where
  (/\) :: l -> l -> l
  infixr 7 /\

instance Semilattice () where
  () /\ () = ()

newtype WrapOrd a = WrapOrd {unwrapOrd :: a}
  deriving (Show, Eq, Ord)

instance (Ord a) => Semilattice (WrapOrd a) where
  (/\) = coerce $ min @a

instance (Ord w) => Semilattice (Min w) where
  (/\) = (<>)

instance (Ord w) => Semilattice (Max w) where
  (/\) = (<>)

instance (Semilattice a, Semilattice b) => Semilattice (a, b) where
  (a1, b1) /\ (a2, b2) = (a1 /\ a2, b1 /\ b2)

instance
  ( Semilattice a
  , Semilattice b
  , Semilattice c
  ) =>
  Semilattice (a, b, c)
  where
  (a1, b1, c1) /\ (a2, b2, c2) = (a1 /\ a2, b1 /\ b2, c1 /\ c2)

instance
  ( Semilattice a
  , Semilattice b
  , Semilattice c
  , Semilattice d
  ) =>
  Semilattice (a, b, c, d)
  where
  (a1, b1, c1, d1) /\ (a2, b2, c2, d2) = (a1 /\ a2, b1 /\ b2, c1 /\ c2, d1 /\ d2)
