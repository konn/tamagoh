{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.Bifunctor qualified as Bi
import Data.EGraph.Immutable qualified as Tamagoh
import Data.Equality.Graph qualified as HeggGraph
import Data.Equality.Matching qualified as Hegg
import Data.Equality.Matching.Database qualified as HeggDB
import Data.Equality.Saturation qualified as Hegg
import Data.Functor.Foldable (Base, Corecursive, cata)
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

data ControlledCase
  = ControlledCase
      String
      (Tamagoh.Term Math)
      (Hegg.Fix Math)
      [Rule]
      Tamagoh.SaturationConfig

controlledCases :: [ControlledCase]
controlledCases =
  [ mkSimplifyDepth 100
  , mkSimplifyDepth 500
  , mkSimplifyGrid 2500 8
  , mkNestedJoin 1500
  , mkRepeatedVar 1500
  , mkMergeRebuild 1500
  ]

controlledConfig :: Tamagoh.SaturationConfig
controlledConfig = Tamagoh.defaultConfig {Tamagoh.nodeLimit = Just 100_000}

mkSimplifyDepth :: Int -> ControlledCase
mkSimplifyDepth depth =
  ControlledCase
    ("simplify-depth-" <> show depth)
    (tame depth)
    (tame depth)
    simplifyRules
    controlledConfig

tame :: (Num f, Corecursive f, Base f ~ Math) => Int -> f
tame depth = tameFrom depth (var "x")

tameFrom :: (Num f) => Int -> f -> f
tameFrom depth = go depth
  where
    go 0 !term = term
    go n !term = go (n - 1) (0 + (1 * term))

mkSimplifyGrid :: Int -> Int -> ControlledCase
mkSimplifyGrid width depth =
  ControlledCase
    ("simplify-grid-" <> show width <> "x" <> show depth)
    (controlledGrid width depth)
    (controlledGrid width depth)
    simplifyRules
    controlledConfig

controlledGrid :: (Num f, Corecursive f, Base f ~ Math) => Int -> Int -> f
controlledGrid width depth =
  case [tameFrom depth (var ("x" <> show i)) | i <- [1 .. width]] of
    [] -> error "controlledGrid: width must be positive"
    term : terms -> foldl' (+) term terms

simplifyRules :: [Rule]
simplifyRules =
  [ named "zero-add" $ 0 + a ==> a
  , named "one-mul" $ 1 * a ==> a
  ]
  where
    a :: Tamagoh.Pattern Math String
    a = Tamagoh.Metavar "a"

mkNestedJoin :: Int -> ControlledCase
mkNestedJoin width =
  ControlledCase
    ("nested-join-" <> show width <> "x2")
    (nestedJoinWorkload width)
    (nestedJoinWorkload width)
    [named "nested-zero-one" $ 0 + (1 * a) ==> a]
    controlledConfig
  where
    a :: Tamagoh.Pattern Math String
    a = Tamagoh.Metavar "a"

nestedJoinWorkload :: (Num f, Corecursive f, Base f ~ Math) => Int -> f
nestedJoinWorkload width =
  inertChain $
    [0 + (1 * var ("m" <> show i)) | i <- [1 .. width]]
      <> [0 + (2 * var ("d" <> show i)) | i <- [1 .. width]]

mkRepeatedVar :: Int -> ControlledCase
mkRepeatedVar width =
  ControlledCase
    ("repeated-var-" <> show width <> "x2")
    (repeatedVarWorkload width)
    (repeatedVarWorkload width)
    [named "double-to-mul" $ a + a ==> 2 * a]
    controlledConfig
  where
    a :: Tamagoh.Pattern Math String
    a = Tamagoh.Metavar "a"

repeatedVarWorkload :: (Num f, Corecursive f, Base f ~ Math) => Int -> f
repeatedVarWorkload width =
  inertChain $
    [let x = var ("r" <> show i) in x + x | i <- [1 .. width]]
      <> [var ("l" <> show i) + var ("r" <> show i) | i <- [1 .. width]]

mkMergeRebuild :: Int -> ControlledCase
mkMergeRebuild width =
  ControlledCase
    ("merge-rebuild-" <> show width <> "x3")
    (mergeRebuildWorkload width)
    (mergeRebuildWorkload width)
    [ named "comm-add" $ a + b ==> b + a
    , named "comm-mul" $ a * b ==> b * a
    , named "sin-involution" $ sin (sin a) ==> a
    ]
    controlledConfig
  where
    a, b :: Tamagoh.Pattern Math String
    a = Tamagoh.Metavar "a"
    b = Tamagoh.Metavar "b"

mergeRebuildWorkload :: (Floating f, Corecursive f, Base f ~ Math) => Int -> f
mergeRebuildWorkload width =
  inertChain $
    [var ("a" <> show i) + var ("b" <> show i) | i <- [1 .. width]]
      <> [var ("c" <> show i) * var ("d" <> show i) | i <- [1 .. width]]
      <> [sin (sin (var ("s" <> show i))) | i <- [1 .. width]]

inertChain :: (Num f) => [f] -> f
inertChain = \case
  [] -> error "inertChain: empty workload"
  term : terms -> foldl' (-) term terms

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
    , bgroup
        "controlled"
        [ env (evaluate $ force $ fmap (toHeggRule @ConstantFold) ruleDefs) \heggRules ->
            env (evaluate $ force $ fmap (toTamagohRule @TamagohAnalysis) ruleDefs) \tamagohRules ->
              bgroup
                name
                [ env (evaluate $ force tamagoh) \term ->
                    bench "tamagoh" $ nf (extractTamagohWith config tamagohRules) term
                , env (evaluate $ force hegg) \term ->
                    bench "hegg" $ nf (extractHegg heggRules) term
                ]
        | ControlledCase name tamagoh hegg ruleDefs config <- controlled
        ]
    ]

annotateControlled ::
  ControlledCase ->
  IO ControlledCase
annotateControlled (ControlledCase name tamagoh hegg ruleDefs config) = do
  let tamagohRules = fmap toTamagohRule ruleDefs
      heggRules = fmap toHeggRule ruleDefs
      tamagohResult@(tamagohBest, tamagohStats) = extractTamagohWithStats config tamagohRules tamagoh
      doubledResult =
        extractTamagohWithStats
          config
            { Tamagoh.maxIterations = Just 60
            , Tamagoh.nodeLimit = Just 200_000
            }
          tamagohRules
          tamagoh
      unlimitedResult =
        extractTamagohWithStats
          config {Tamagoh.maxIterations = Nothing, Tamagoh.nodeLimit = Nothing}
          tamagohRules
          tamagoh
      (heggBest, heggGraphStats) = extractHeggWithStats heggRules hegg
      sameBest = fmap toCommonTamagoh tamagohBest == fmap toCommonHegg heggBest
  if tamagohResult /= doubledResult || tamagohResult /= unlimitedResult
    then error $ "controlled benchmark budget instability: " <> show (name, tamagohResult, doubledResult, unlimitedResult)
    else
      if tamagohStats /= heggGraphStats
        then error $ "controlled benchmark graph-size mismatch: " <> show (name, tamagohStats, heggGraphStats)
        else
          if not sameBest
            then error $ "controlled benchmark extracted-result mismatch: " <> show name
            else
              pure $
                ControlledCase
                  (name <> "-nodes-" <> show (fst tamagohStats) <> "-classes-" <> show (snd tamagohStats))
                  tamagoh
                  hegg
                  ruleDefs
                  config

newtype CommonMath = CommonMath (Math CommonMath)
  deriving (Eq, Show)

toCommonTamagoh :: Tamagoh.Term Math -> CommonMath
toCommonTamagoh = cata CommonMath

toCommonHegg :: Hegg.Fix Math -> CommonMath
toCommonHegg = cata CommonMath

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
