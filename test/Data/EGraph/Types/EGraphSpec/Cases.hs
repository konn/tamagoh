{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.Types.EGraphSpec.Cases (
  module Data.EGraph.Types.EGraphSpec.Cases,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Orphans
import Control.Syntax.DataFlow qualified as DataFlow
import Data.EGraph.Types
import Data.Functor.Classes
import Data.Hashable
import Data.Hashable.Lifted
import Data.Unrestricted.Linear (AsMovable (..))
import GHC.Generics qualified as GHC
import Generics.Linear.TH qualified as GLC
import Prelude.Linear
import Prelude.Linear.Generically qualified as GLC
import Text.Show.Deriving (deriveShow1)
import Prelude qualified as P

data Expr l = Add l l | Mul l l | Lit Int | Var String
  deriving
    ( P.Eq
    , P.Ord
    , GHC.Generic
    , GHC.Generic1
    , P.Functor
    , P.Foldable
    , P.Traversable
    , Show
    )
  deriving (Eq1, Ord1) via GHC.Generically1 Expr
  deriving anyclass (Hashable, Hashable1)

GLC.deriveGenericAnd1 ''Expr
deriveShow1 ''Expr

deriving via GLC.Generically1 Expr instance Movable1 Expr

add :: Term Expr %1 -> Term Expr %1 -> Term Expr
add x y = wrapTerm $ Add x y

mul :: Term Expr %1 -> Term Expr %1 -> Term Expr
mul x y = wrapTerm $ Mul x y

lit :: Int %1 -> Term Expr
lit = wrapTerm . Lit

var :: String %1 -> Term Expr
var = wrapTerm . Var

instance Additive (Term Expr) where
  (+) = add

instance Multiplicative (Term Expr) where
  (*) = mul

instance FromInteger (Term Expr) where
  fromInteger = lit . fromInteger

instance P.Num (Term Expr) where
  l + r = add l r
  l * r = mul l r
  negate _ = P.error "negate is not supported"
  abs _ = P.error "abs is not supported"
  signum _ = P.error "signum is not supported"
  fromInteger n = lit (P.fromInteger n)

a :: Term Expr
a = var "a"

b :: Term Expr
b = var "b"

c :: Term Expr
c = var "c"

aPLUSb :: Term Expr
aPLUSb = a + b

aPLUSc :: Term Expr
aPLUSc = a + c

data Case1Result = Case1Result
  { abacEqAtFirst :: !(Maybe Bool)
  , abacEqAfterMerge :: !(Maybe Bool)
  , initAId :: !EClassId
  , initBId :: !EClassId
  , initCId :: !EClassId
  , initABId :: !EClassId
  , initACId :: !EClassId
  , unionedBorCId :: !(Maybe EClassId)
  }
  deriving (P.Show, P.Eq, GHC.Generic)

GLC.deriveGeneric ''Case1Result

deriving via AsMovable Case1Result instance Consumable Case1Result

deriving via AsMovable Case1Result instance Dupable Case1Result

deriving via GLC.Generically Case1Result instance Movable Case1Result

case1 :: Mut α (EGraph Expr) %1 -> BO α (Ur Case1Result)
case1 egraph = Control.do
  (Ur abNode, Ur initABId, egraph) <- fromTerm egraph aPLUSb
  (Ur acNode, Ur initACId, egraph) <- fromTerm egraph aPLUSc
  (Ur abacEqAtFirst, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph abNode acNode
  (Ur initAId, egraph) <- addNode egraph (ENode (Var "a"))
  (Ur initBId, egraph) <- addNode egraph (ENode (Var "b"))
  (Ur initCId, egraph) <- addNode egraph (ENode (Var "c"))
  (Ur unionedBorCId, egraph) <- merge initBId initCId egraph
  egraph <- rebuild egraph
  (Ur abacEqAfterMerge, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph abNode acNode
  egraph `lseq` Control.pure (Ur Case1Result {..})

withNewEGraph ::
  (forall α. Mut α (EGraph Expr) %1 -> BO α (Ur a)) %1 ->
  Linearly %1 ->
  a
withNewEGraph f lin = DataFlow.do
  (v, graph) <- modifyLinearOnlyBO (new lin) f
  graph `lseq` unur v
