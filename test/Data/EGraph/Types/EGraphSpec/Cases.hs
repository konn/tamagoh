{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -ddump-prep -ddump-to-file -ddump-rules -dsuppress-idinfo -dsuppress-coercions -dsuppress-type-applications -dsuppress-module-prefixes -dsuppress-type-signatures -dsuppress-uniques #-}

module Data.EGraph.Types.EGraphSpec.Cases (
  module Data.EGraph.Types.EGraphSpec.Cases,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.EGraph.Types
import Data.Fix (Fix (..))
import Data.Functor.Classes
import Data.Hashable
import Data.Hashable.Lifted
import Data.Maybe (fromJust)
import Data.Unrestricted.Linear (AsMovable (..))
import Data.Unrestricted.Linear.Lifted
import GHC.Generics qualified as GHC
import Generics.Linear.TH qualified as GLC
import Prelude.Linear
import Prelude.Linear.Generically qualified as GLC
import Text.Show.Borrowed (display)
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

deriving via GLC.Generically1 Expr instance Copyable1 Expr

add :: Term Expr %1 -> Term Expr %1 -> Term Expr
add x y = Fix $ Add x y

mul :: Term Expr %1 -> Term Expr %1 -> Term Expr
mul x y = Fix $ Mul x y

lit :: Int %1 -> Term Expr
lit = Fix . Lit

var :: String %1 -> Term Expr
var = Fix . Var

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

newtype RawString = RawString String
  deriving newtype (P.Eq, Movable, Consumable, Dupable)

instance Show RawString where
  showsPrec _ (RawString s) = showString s

data Case1Result = Case1Result
  { initEGraph :: !RawString
  , abacEqAtFirst :: !(Maybe Bool)
  , abacEqAfterMerge :: !(Maybe Bool)
  , initAId :: !(Maybe EClassId)
  , initBId :: !(Maybe EClassId)
  , initCId :: !(Maybe EClassId)
  , initABId :: !EClassId
  , initACId :: !EClassId
  , unionedBorCId :: !(Maybe EClassId)
  , finalEGraph :: !RawString
  }
  deriving (P.Show, P.Eq, GHC.Generic)

GLC.deriveGeneric ''Case1Result

deriving via AsMovable Case1Result instance Consumable Case1Result

deriving via AsMovable Case1Result instance Dupable Case1Result

deriving via GLC.Generically Case1Result instance Movable Case1Result

data MiniCaseResult = MiniCaseResult
  { initEGraph :: !RawString
  , abEqAtFst :: !(Maybe Bool)
  , initAId :: !EClassId
  , initBId :: !EClassId
  , abEqAtLast :: !(Maybe Bool)
  , unionedAorBId :: !(Maybe EClassId)
  , lastAId :: !(Maybe EClassId)
  , lastBId :: !(Maybe EClassId)
  , finalEGraph :: !RawString
  }
  deriving (P.Show, P.Eq, GHC.Generic)

GLC.deriveGeneric ''MiniCaseResult

deriving via AsMovable MiniCaseResult instance Consumable MiniCaseResult

deriving via AsMovable MiniCaseResult instance Dupable MiniCaseResult

deriving via GLC.Generically MiniCaseResult instance Movable MiniCaseResult

caseABUnion :: Mut α (EGraph Expr) %1 -> BO α (Ur MiniCaseResult)
caseABUnion egraph = Control.do
  (Ur (RawString -> initEGraph), egraph) <- sharing egraph $ \egraph -> display egraph
  (Ur aNode, Ur initAId, egraph) <- addTerm egraph a
  (Ur bNode, Ur initBId, egraph) <- addTerm egraph b
  (Ur abEqAtFst, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph aNode bNode
  (Ur unionedAorBId, egraph) <- merge initAId initBId egraph
  egraph <- rebuild egraph
  (Ur abEqAtLast, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph aNode bNode
  (Ur lastAId, egraph) <- addNode egraph aNode
  (Ur lastBId, egraph) <- addNode egraph bNode
  (Ur (RawString -> finalEGraph), egraph) <- sharing egraph $ \egraph -> display egraph
  egraph `lseq` Control.pure (Ur MiniCaseResult {..})

caseA5Union :: Mut α (EGraph Expr) %1 -> BO α (Ur MiniCaseResult)
caseA5Union egraph = Control.do
  (Ur (RawString -> initEGraph), egraph) <- sharing egraph $ \egraph -> display egraph
  (Ur aNode, Ur initAId, egraph) <- addTerm egraph a
  (Ur bNode, Ur initBId, egraph) <- addTerm egraph 5
  (Ur abEqAtFst, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph aNode bNode
  (Ur unionedAorBId, egraph) <- merge initAId initBId egraph
  egraph <- rebuild egraph
  (Ur abEqAtLast, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph aNode bNode
  (Ur lastAId, egraph) <- addNode egraph aNode
  (Ur lastBId, egraph) <- addNode egraph bNode
  (Ur (RawString -> finalEGraph), egraph) <- sharing egraph $ \egraph -> display egraph
  egraph `lseq` Control.pure (Ur MiniCaseResult {..})

caseABvsAC :: Mut α (EGraph Expr) %1 -> BO α (Ur Case1Result)
caseABvsAC egraph = Control.do
  (Ur (RawString -> initEGraph), egraph) <- sharing egraph $ \egraph -> display egraph
  (Ur abNode, Ur initABId, egraph) <- addTerm egraph $ a + b
  (Ur acNode, Ur initACId, egraph) <- addTerm egraph $ a + c
  (Ur abacEqAtFirst, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph abNode acNode
  (Ur initAId, egraph) <- addNode egraph (ENode (Var "a"))
  (Ur initBId, egraph) <- addNode egraph (ENode (Var "b"))
  (Ur initCId, egraph) <- addNode egraph (ENode (Var "c"))
  (Ur unionedBorCId, egraph) <- merge (fromJust initBId) (fromJust initCId) egraph
  egraph <- rebuild egraph
  (Ur abacEqAfterMerge, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph abNode acNode
  (Ur (RawString -> finalEGraph), egraph) <- sharing egraph $ \egraph -> display egraph
  egraph `lseq` Control.pure (Ur Case1Result {..})

caseABvsA5 :: Mut α (EGraph Expr) %1 -> BO α (Ur Case1Result)
caseABvsA5 egraph = Control.do
  (Ur (RawString -> initEGraph), egraph) <- sharing egraph $ \egraph -> display egraph
  (Ur abNode, Ur initABId, egraph) <- addTerm egraph $ a + b
  (Ur acNode, Ur initACId, egraph) <- addTerm egraph $ a + 5
  (Ur abacEqAtFirst, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph abNode acNode
  (Ur initAId, egraph) <- addNode egraph (ENode (Var "a"))
  (Ur initBId, egraph) <- addNode egraph (ENode (Var "b"))
  (Ur initCId, egraph) <- addNode egraph (ENode (Lit 5))
  (Ur unionedBorCId, egraph) <- merge (fromJust initBId) (fromJust initCId) egraph
  egraph <- rebuild egraph
  (Ur abacEqAfterMerge, egraph) <- sharing egraph \egraph -> Control.do
    equivalent egraph abNode acNode
  (Ur (RawString -> finalEGraph), egraph) <- sharing egraph $ \egraph -> display egraph
  egraph `lseq` Control.pure (Ur Case1Result {..})