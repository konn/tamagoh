{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.EGraph.ImmutableSpec (module Data.EGraph.ImmutableSpec) where

import Control.Functor.Linear qualified as Control
import Data.Deriving (deriveShow1)
import Data.EGraph.Immutable
import Data.EGraph.Types.EGraph qualified as MEG
import Data.EGraph.Types.Language (Matchable)
import Data.Functor.Classes (Eq1, Ord1)
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1)
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)
import GHC.Generics hiding ((:*:))
import Generics.Linear.TH qualified as GLC
import Prelude.Linear (Consumable (..), Ur (..))
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (lookup)

data Expr a = a :+ a | a :* a | Lit Int | Var String
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Generic1)
  deriving (Eq1, Ord1, HasDatabase, Matchable) via Generically1 Expr
  deriving anyclass (Hashable, Hashable1)

deriveShow1 ''Expr
GLC.deriveGenericAnd1 ''Expr

deriving via Generically1 Expr instance Movable1 Expr

deriving via Generically1 Expr instance Copyable1 Expr

var :: String -> Term Expr
var = wrapTerm . Var

instance Num (Term Expr) where
  (+) = fmap wrapTerm . (:+)
  (*) = fmap wrapTerm . (:*)
  fromInteger n = wrapTerm $ Lit (fromInteger n)
  negate _ = error "negate is not supported"
  abs _ = error "abs is not supported"
  signum _ = error "signum is not supported"

instance Num (Pattern Expr v) where
  (+) = fmap PNode . (:+)
  (*) = fmap PNode . (:*)
  fromInteger n = PNode $ Lit (fromInteger n)
  negate _ = error "negate is not supported"
  abs _ = error "abs is not supported"
  signum _ = error "signum is not supported"

graph1 :: EGraph Expr
graph1 = fromList [(a + b) * c]
  where
    a = var "a"
    b = var "b"
    c = var "c"

ringRules :: [Rule Expr String]
ringRules =
  [ named "+-comm" $ a + b ==> b + a
  , named "*-comm" $ a * b ==> b * a
  , named "+-assoc-r" $ (a + b) + c ==> a + (b + c)
  , named "+-assoc-l" $ a + (b + c) ==> (a + b) + c
  , named "*-assoc-r" $ (a * b) * c ==> a * (b * c)
  , named "*-assoc-l" $ a * (b * c) ==> (a * b) * c
  , named "distrib" $ a * (b + c) ==> a * b + a * c
  , named "add-zero" $ a + 0 ==> a
  , named "mul-one" $ a * 1 ==> a
  , named "mul-zero" $ 0 * a ==> 0
  ]
  where
    pvar :: String -> Pattern Expr String
    pvar = Metavar

    a = pvar "a"
    b = pvar "b"
    c = pvar "c"

test_saturate :: TestTree
test_saturate =
  testGroup
    "saturate"
    [ testCaseSteps "(a + b) * c == c * b + a * c" \step -> do
        step "Adding terms..."
        let Ur graph =
              modify
                ( \eg -> Control.do
                    (Ur _, Ur _, eg) <- MEG.addTerm eg ((a + b) * c)
                    (Ur _, Ur _, eg) <- MEG.addTerm eg (c * b + a * c)
                    Control.pure (consume eg)
                )
                graph1
            lhs = lookupTerm ((a + b) * c) graph
            rhs = lookupTerm (c * b + a * c) graph
        case (lhs, rhs) of
          (Nothing, Nothing) -> assertFailure "Terms not found"
          (Just _, Nothing) -> assertFailure "RHS term not found"
          (Nothing, Just _) -> assertFailure "LHS term not found"
          (Just l, Just r) -> do
            step "Checking (non-)equivalence before saturation..."
            equivalent graph l r @?= Just False
            step "Saturating..."
            let result = saturate SaturationConfig {maxIterations = Nothing} ringRules graph
            step "Checking equivalence after saturation"
            case result of
              Left err -> assertFailure $ "saturation failed: " <> show err
              Right graph' -> equivalent graph' l r @?= Just True
    ]
  where
    a = var "a"
    b = var "b"
    c = var "c"
