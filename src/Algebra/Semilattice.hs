{-# LANGUAGE DerivingStrategies #-}

module Algebra.Semilattice (Semilattice (..), WrapOrd (..)) where

import Data.Coerce (coerce)

{- | (Unbounded) meet-semilattice.

Laws:

   * Associativity: @a '/\' (b '/\' c) = (a '/\' b) '/\' c@
   * Commutativity: @a '/\' b = b '/\' a@
   * Idempotency: @a '/\' a = a@
-}
class Semilattice l where
  (/\) :: l -> l -> l
  infixr 7 /\

instance Semilattice () where
  () /\ () = ()

newtype WrapOrd a = WrapOrd {unwrapOrd :: a}
  deriving (Show, Eq, Ord)

instance (Ord a) => Semilattice (WrapOrd a) where
  (/\) = coerce $ min @a