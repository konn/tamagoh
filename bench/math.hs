{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.Bifunctor qualified as Bi
import Data.EGraph.Immutable qualified as Tamagoh
import Data.Equality.Saturation qualified as Hegg
import Data.Functor.Foldable (Base, Corecursive)
import Data.Maybe (fromJust)
import Tamagoh.Bench.Math
import Test.Tasty.Bench

cases :: [(String, Tamagoh.Term Math, Hegg.Fix Math)]
cases =
  [ mk "i1" $ integral 1 x
  , mk "i2" $ integral (cos x) x
  , mk "i3" $ integral (x ** 1) x
  , mk "i4" $ integral (x * cos x) x
  , mk "i5" $ integral (cos x * x) x
  , mk "i6" $ integral (log x) x
  ]
  where
    x :: (Corecursive f, Base f ~ Math) => f
    x = var "x"

mk :: String -> (forall f. (Floating f, Corecursive f, Base f ~ Math) => f) -> (String, Tamagoh.Term Math, Hegg.Fix Math)
mk name term = (name, term, term)

main :: IO ()
main =
  defaultMain
    [ env (evaluate $ force $ mathRulesHegg @ConstantFold) \heggRules ->
        env (evaluate $ force $ mathRulesTamagoh @TamagohAnalysis) \tamagohRules ->
          bgroup
            "math"
            [ bgroup name $
                [ env (evaluate $ force $ tamagoh) \term ->
                    bench "tamagoh" $ nf (extractTamagoh tamagohRules) term
                , env (evaluate $ force $ hegg) \term ->
                    bench "hegg" $ nf (extractHegg heggRules) term
                ]
            | (name, tamagoh, hegg) <- cases
            ]
    ]

type TamagohAnalysis = (Tamagoh.ExtractBest Math BenchCost, ConstantFold)

extractHegg ::
  [Hegg.Rewrite ConstantFold Math] ->
  Hegg.Fix Math ->
  Either () (Hegg.Fix Math)
extractHegg rs term =
  Right $ fst $ Hegg.equalitySaturation term rs symCost

extractTamagoh ::
  [Tamagoh.Rule Math TamagohAnalysis String] ->
  Tamagoh.Term Math ->
  Either () (Tamagoh.Term Math)
extractTamagoh rs node =
  let gr0 = Tamagoh.fromList [node]
      !eid = fromJust $ Tamagoh.lookupTerm node gr0
   in Bi.bimap
        (const ())
        (fst . fromJust . Tamagoh.extractBest eid)
        $ Tamagoh.saturate Tamagoh.defaultConfig rs gr0
