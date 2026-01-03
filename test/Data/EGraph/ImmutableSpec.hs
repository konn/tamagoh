{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.ImmutableSpec (module Data.EGraph.ImmutableSpec) where

import Control.Functor.Linear qualified as Control
import Data.EGraph.Immutable
import Data.EGraph.Types.EGraph qualified as MEG
import Data.EGraph.Types.Language (deriveLanguage)
import Data.Hashable (Hashable)
import GHC.Generics hiding ((:*:))
import Prelude.Linear (Consumable (..), Ur (..))
import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (lookup)

data Expr a = a :+ a | a :* a | Lit Int | Var String
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Generic1)
  deriving anyclass (Hashable)

deriveLanguage ''Expr

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

graph1 :: EGraph () Expr
graph1 = empty

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
        step "Checking term polution..."
        let lhs = (a + b) * c
            rhs = c * b + a * c
        lookupTerm lhs graph1 @?= Nothing
        lookupTerm rhs graph1 @?= Nothing
        step "Adding terms..."
        let Ur graph =
              modify
                ( \eg -> Control.do
                    (Ur _, Ur _, eg) <- MEG.addTerm eg lhs
                    (Ur _, Ur _, eg) <- MEG.addTerm eg rhs
                    Control.pure (consume eg)
                )
                graph1
            lid = lookupTerm lhs graph
            rid = lookupTerm rhs graph
        case (lid, rid) of
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
    , testCaseSteps "(a + 0 + b) * c == c * b + a * c" \step -> do
        step "Checking term polution..."
        let lhs = ((a + 0 + b) * c)
            rhs = (c * b + a * c)
            lid = lookupTerm lhs graph1
            rid = lookupTerm rhs graph1
        lid @?= Nothing
        rid @?= Nothing
        step "Adding terms..."
        let Ur graph =
              modify
                ( \eg -> Control.do
                    (Ur _, Ur _, eg) <- MEG.addTerm eg lhs
                    Control.pure (consume eg)
                )
                graph1
            lid = lookupTerm lhs graph
            rid = lookupTerm rhs graph
        case (lid, rid) of
          (Nothing, Nothing) -> assertFailure "Terms not found"
          (_, Just _) -> assertFailure "RHS term should not be registered, but found!"
          (Just l, Nothing) -> do
            step "Saturating..."
            let result = saturate SaturationConfig {maxIterations = Nothing} ringRules graph
            step "Checking equivalence after saturation"
            case result of
              Left err -> assertFailure $ "saturation failed: " <> show err
              Right graph' -> do
                let rid = lookupTerm rhs graph'
                case rid of
                  Nothing -> assertFailure "RHS term not found after saturation"
                  Just r -> equivalent graph' l r @?= Just True
    ]
  where
    a = var "a"
    b = var "b"
    c = var "c"
