{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.Bifunctor qualified as Bi
import Data.EGraph.Immutable qualified as Tamagoh
import Data.Equality.Graph qualified as HeggGraph
import Data.Equality.Matching qualified as Hegg
import Data.Equality.Matching.Database qualified as HeggDB
import Data.Equality.Saturation qualified as Hegg
import Data.Functor.Foldable (Base, Corecursive)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Tamagoh.Bench.Math
import Test.Tasty.Bench

integrationCases :: [(String, Tamagoh.Term Math, Hegg.Fix Math)]
integrationCases =
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

controlledCases :: [(String, Tamagoh.Term Math, Hegg.Fix Math)]
controlledCases = [mkControlled 100, mkControlled 500, mkControlledGrid 2500 8]

controlledConfig :: Tamagoh.SaturationConfig
controlledConfig = Tamagoh.defaultConfig {Tamagoh.nodeLimit = Just 100_000}

mkControlled :: Int -> (String, Tamagoh.Term Math, Hegg.Fix Math)
mkControlled depth = ("depth-" <> show depth, tame depth, tame depth)

tame :: (Num f, Corecursive f, Base f ~ Math) => Int -> f
tame depth = tameFrom depth (var "x")

tameFrom :: (Num f) => Int -> f -> f
tameFrom depth = go depth
  where
    go 0 !term = term
    go n !term = go (n - 1) (0 + (1 * term))

mkControlledGrid :: Int -> Int -> (String, Tamagoh.Term Math, Hegg.Fix Math)
mkControlledGrid width depth =
  ( "grid-" <> show width <> "x" <> show depth
  , controlledGrid width depth
  , controlledGrid width depth
  )

controlledGrid :: (Num f, Corecursive f, Base f ~ Math) => Int -> Int -> f
controlledGrid width depth =
  case [tameFrom depth (var ("x" <> show i)) | i <- [1 .. width]] of
    [] -> error "controlledGrid: width must be positive"
    term : terms -> foldl' (+) term terms

controlledRuleDefs :: [Rule]
controlledRuleDefs =
  [ named "zero-add" $ 0 + a ==> a
  , named "one-mul" $ 1 * a ==> a
  ]
  where
    a :: Tamagoh.Pattern Math String
    a = Tamagoh.Metavar "a"

mk :: String -> (forall f. (Floating f, Corecursive f, Base f ~ Math) => f) -> (String, Tamagoh.Term Math, Hegg.Fix Math)
mk name term = (name, term, term)

main :: IO ()
main = do
  controlled <- traverse annotateControlled controlledCases
  defaultMain
    [ env (evaluate $ force $ mathRulesHegg @ConstantFold) \heggRules ->
        env (evaluate $ force $ mathRulesTamagoh @TamagohAnalysis) \tamagohRules ->
          bgroup
            "integration"
            [ bgroup name $
                [ env (evaluate $ force $ tamagoh) \term ->
                    bench "tamagoh" $ nf (extractTamagoh tamagohRules) term
                , env (evaluate $ force $ hegg) \term ->
                    bench "hegg" $ nf (extractHegg heggRules) term
                ]
            | (name, tamagoh, hegg) <- integrationCases
            ]
    , env (evaluate $ force $ fmap (toHeggRule @ConstantFold) controlledRuleDefs) \heggRules ->
        env (evaluate $ force $ fmap (toTamagohRule @TamagohAnalysis) controlledRuleDefs) \tamagohRules ->
          bgroup
            "controlled"
            [ bgroup
                name
                [ env (evaluate $ force tamagoh) \term ->
                    bench "tamagoh" $ nf (extractTamagohWith controlledConfig tamagohRules) term
                , env (evaluate $ force hegg) \term ->
                    bench "hegg" $ nf (extractHegg heggRules) term
                ]
            | (name, tamagoh, hegg) <- controlled
            ]
    ]

annotateControlled ::
  (String, Tamagoh.Term Math, Hegg.Fix Math) ->
  IO (String, Tamagoh.Term Math, Hegg.Fix Math)
annotateControlled (name, tamagoh, hegg) = do
  let tamagohStats = snd $ extractTamagohWithStats controlledConfig (fmap toTamagohRule controlledRuleDefs) tamagoh
      heggGraphStats = snd $ extractHeggWithStats (fmap toHeggRule controlledRuleDefs) hegg
  if tamagohStats == heggGraphStats
    then pure (name <> "-nodes-" <> show (fst tamagohStats) <> "-classes-" <> show (snd tamagohStats), tamagoh, hegg)
    else error $ "controlled benchmark graph-size mismatch: " <> show (name, tamagohStats, heggGraphStats)

-- Mirror hegg/egg exactly: saturate with ConstantFold only and extract
-- post-hoc ('extractBestWith'), instead of maintaining ExtractBest as a
-- per-merge analysis during saturation.
type TamagohAnalysis = ConstantFold

extractHegg ::
  [Hegg.Rewrite ConstantFold Math] ->
  Hegg.Fix Math ->
  Either () (Hegg.Fix Math)
extractHegg rs term =
  Right $ fst $ Hegg.equalitySaturation term rs symCost

extractHeggWithStats ::
  [Hegg.Rewrite ConstantFold Math] ->
  Hegg.Fix Math ->
  (Either () (Hegg.Fix Math), (Int, Int))
extractHeggWithStats rs term =
  let (!best, !graph) = Hegg.equalitySaturation term rs symCost
   in (Right best, heggStats graph)

heggStats :: HeggGraph.EGraph ConstantFold Math -> (Int, Int)
heggStats graph = databaseStats graph $ Hegg.eGraphToDatabase graph

databaseStats :: HeggGraph.EGraph ConstantFold Math -> HeggDB.Database Math -> (Int, Int)
databaseStats graph (HeggDB.DB relations) =
  ( sum $ trieLeaves <$> Map.elems relations
  , IntSet.size $ IntSet.map (`HeggGraph.find` graph) rawClassIds
  )
  where
    rawClassIds = IntSet.unions $ HeggDB.tkeys <$> Map.elems relations
    trieLeaves (HeggDB.MkIntTrie _ children)
      | IntMap.null children = 1
      | otherwise = sum $ trieLeaves <$> IntMap.elems children

extractTamagoh ::
  [Tamagoh.Rule Math TamagohAnalysis String] ->
  Tamagoh.Term Math ->
  Either () (Tamagoh.Term Math)
extractTamagoh = extractTamagohWith Tamagoh.defaultConfig

extractTamagohWith ::
  Tamagoh.SaturationConfig ->
  [Tamagoh.Rule Math TamagohAnalysis String] ->
  Tamagoh.Term Math ->
  Either () (Tamagoh.Term Math)
extractTamagohWith config rs node =
  Bi.bimap
    (const ())
    ( \(gr, eids) -> case eids of
        eid : _ -> fst $ fromJust $ Tamagoh.extractBestWith @BenchCost eid gr
        [] -> error "saturateFromList returned no id for one input term"
    )
    $ Tamagoh.saturateFromList config rs [node]

extractTamagohWithStats ::
  Tamagoh.SaturationConfig ->
  [Tamagoh.Rule Math TamagohAnalysis String] ->
  Tamagoh.Term Math ->
  (Either () (Tamagoh.Term Math), (Int, Int))
extractTamagohWithStats config rs node =
  case Tamagoh.saturateFromList config rs [node] of
    Left _ -> (Left (), (0, 0))
    Right (gr, eid : _) ->
      ( Right $ fst $ fromJust $ Tamagoh.extractBestWith @BenchCost eid gr
      , (Tamagoh.size gr, Tamagoh.numEClasses gr)
      )
    Right (_, []) -> error "saturateFromList returned no id for one input term"
