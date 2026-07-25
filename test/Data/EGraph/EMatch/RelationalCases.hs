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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.EMatch.RelationalCases (
  module Data.EGraph.EMatch.RelationalCases,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Orphans ()
import Control.Monad.Borrow.Pure.Utils
import Data.EGraph.EMatch.Relational
import Data.EGraph.EMatch.Relational.Database qualified as Database
import Data.EGraph.EMatch.Relational.Query qualified as Query
import Data.EGraph.EMatch.Types
import Data.EGraph.Saturation qualified as Saturation
import Data.EGraph.Types
import Data.EGraph.Types.Language (deriveLanguage)
import Data.Functor.Linear qualified as Data
import Data.HashSet qualified as HS
import Data.IntMap.Strict qualified as IM
import Data.IntSet qualified as IS
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromJust, listToMaybe)
import Data.Trie qualified as Trie
import Data.Vector qualified as V
import GHC.Generics qualified as GHC
import Prelude.Linear
import Prelude qualified as P

data Lang1 a = F !a !a | G !a | I !Int
  deriving
    ( P.Eq
    , P.Ord
    , P.Show
    , P.Functor
    , P.Foldable
    , P.Traversable
    )

deriveLanguage ''Lang1

data PlannerLang a
  = PAdd !a !a
  | PMul !a !a
  | POuter !a
  | PInner !a
  | PLit !Int
  deriving
    ( P.Eq
    , P.Ord
    , P.Show
    , P.Functor
    , P.Foldable
    , P.Traversable
    )

deriveLanguage ''PlannerLang

data PreparedTransposePin = PreparedTransposePin
  { nestedOrderExact :: !P.Bool
  , nestedRawSizeExact :: !P.Bool
  , staticOrderExact :: !P.Bool
  , atomCountEligibilityExact :: !P.Bool
  , layoutValidationExact :: !P.Bool
  , repeatedVariableExact :: !P.Bool
  , fixedColumnFallbackExact :: !P.Bool
  , identityLayoutExact :: !P.Bool
  , missingRelationExact :: !P.Bool
  , unaryChainEligibilityExact :: !P.Bool
  }
  deriving (P.Eq, P.Show)

preparedTransposePin :: PreparedTransposePin
preparedTransposePin =
  let nestedPatQuery =
        Query.Conj $
          [4]
            Query.::- ( Query.Atom (Query.MkRel (Query.QVar 0) (PAdd (Query.QVar 1) (Query.QVar 2)))
                          NE.:| [ Query.Atom (Query.MkRel (Query.QVar 1) (PLit 0))
                                , Query.Atom (Query.MkRel (Query.QVar 2) (PMul (Query.QVar 3) (Query.QVar 4)))
                                , Query.Atom (Query.MkRel (Query.QVar 3) (PLit 1))
                                ]
                      )
      nestedQuery =
        Query.PatternQuery
          { Query.root = 0
          , Query.varNames = V.fromList [Nothing, Nothing, Nothing, Nothing, Just "x"]
          , Query.patQuery = nestedPatQuery
          }
      nestedDb =
        Database.fromRelations
          [ Query.MkRel 100 (PAdd 10 20)
          , Query.MkRel 101 (PAdd 10 30)
          , Query.MkRel 10 (PLit 0)
          , Query.MkRel 20 (PMul 50 200)
          , Query.MkRel 30 (PMul 40 300)
          , Query.MkRel 40 (PLit 1)
          , Query.MkRel 50 (PLit 1)
          ]
      nestedExpected =
        [ (100, IM.fromList [(0, 100), (1, 10), (2, 20), (3, 50), (4, 200)])
        , (101, IM.fromList [(0, 101), (1, 10), (2, 30), (3, 40), (4, 300)])
        ]
      nestedCanonical = ematchDbWithCount nestedQuery nestedDb
      nestedPrepared =
        ematchPreparedDbWithCount (prepare nestedQuery) nestedDb

      repeatedQuery =
        Query.PatternQuery
          { Query.root = 0
          , Query.varNames = V.empty
          , Query.patQuery =
              Query.Conj $
                []
                  Query.::- ( Query.Atom (Query.MkRel (Query.QVar 0) (PAdd (Query.QVar 1) (Query.QVar 1)))
                                NE.:| [ Query.Atom (Query.MkRel (Query.QVar 1) (PLit 0))
                                      , Query.Atom (Query.MkRel (Query.QVar 1) (PLit 0))
                                      ]
                            )
          }
      repeatedDb =
        Database.fromRelations
          [ Query.MkRel 100 (PAdd 10 10)
          , Query.MkRel 101 (PAdd 10 11)
          , Query.MkRel 10 (PLit 0)
          ]
      repeatedCanonical = ematchDbWithCount repeatedQuery repeatedDb
      repeatedPrepared =
        ematchPreparedDbWithCount (prepare repeatedQuery) repeatedDb

      fixedQuery =
        Query.PatternQuery
          { Query.root = 0
          , Query.varNames = V.empty
          , Query.patQuery =
              Query.Conj $
                []
                  Query.::- ( Query.Atom (Query.MkRel (Query.QVar 0) (PAdd (Query.QVar 1) (Query.EId 99)))
                                NE.:| [ Query.Atom (Query.MkRel (Query.QVar 1) (PLit 0))
                                      , Query.Atom (Query.MkRel (Query.QVar 1) (PLit 0))
                                      ]
                            )
          }
      fixedDb =
        Database.fromRelations
          [ Query.MkRel 100 (PAdd 10 99)
          , Query.MkRel 10 (PLit 0)
          ]
      fixedCanonical = ematchDbWithCount fixedQuery fixedDb
      fixedPrepared =
        ematchPreparedDbWithCount (prepare fixedQuery) fixedDb

      identityQuery =
        Query.PatternQuery
          { Query.root = 0
          , Query.varNames = V.empty
          , Query.patQuery =
              Query.Conj $
                []
                  Query.::- ( Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0))
                                NE.:| [ Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0))
                                      , Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0))
                                      ]
                            )
          }
      identityDb = Database.fromRelations [Query.MkRel 10 (PLit 0)]
      identityCanonical = ematchDbWithCount identityQuery identityDb
      identityPrepared =
        ematchPreparedDbWithCount (prepare identityQuery) identityDb

      oneAtomQuery =
        nestedQuery
          { Query.patQuery =
              Query.Conj $
                []
                  Query.::- (Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0)) NE.:| [])
          }
      twoAtomQuery =
        nestedQuery
          { Query.patQuery =
              Query.Conj $
                []
                  Query.::- ( Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0))
                                NE.:| [Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0))]
                            )
          }
      threeAtomQuery = identityQuery
      headOnlyQuery =
        identityQuery
          { Query.patQuery =
              Query.Conj $
                [9]
                  Query.::- ( Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0))
                                NE.:| [ Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0))
                                      , Query.Atom (Query.MkRel (Query.QVar 0) (PLit 0))
                                      ]
                            )
          }
      unaryChainQuery atoms =
        nestedQuery
          { Query.patQuery = Query.Conj $ [] Query.::- atoms
          }
      directedUnaryQuery =
        unaryChainQuery
          ( Query.Atom (Query.MkRel (Query.QVar 0) (POuter (Query.QVar 1)))
              NE.:| [Query.Atom (Query.MkRel (Query.QVar 1) (PInner (Query.QVar 2)))]
          )
      disconnectedUnaryQuery =
        unaryChainQuery
          ( Query.Atom (Query.MkRel (Query.QVar 0) (POuter (Query.QVar 1)))
              NE.:| [Query.Atom (Query.MkRel (Query.QVar 2) (PInner (Query.QVar 3)))]
          )
      repeatedUnaryQuery =
        unaryChainQuery
          ( Query.Atom (Query.MkRel (Query.QVar 0) (POuter (Query.QVar 0)))
              NE.:| [Query.Atom (Query.MkRel (Query.QVar 0) (PInner (Query.QVar 1)))]
          )
      sharedChildUnaryQuery =
        unaryChainQuery
          ( Query.Atom (Query.MkRel (Query.QVar 0) (POuter (Query.QVar 2)))
              NE.:| [Query.Atom (Query.MkRel (Query.QVar 1) (PInner (Query.QVar 2)))]
          )
      sharedRootUnaryQuery =
        unaryChainQuery
          ( Query.Atom (Query.MkRel (Query.QVar 2) (POuter (Query.QVar 0)))
              NE.:| [Query.Atom (Query.MkRel (Query.QVar 2) (PInner (Query.QVar 1)))]
          )
      cyclicUnaryQuery =
        unaryChainQuery
          ( Query.Atom (Query.MkRel (Query.QVar 0) (POuter (Query.QVar 1)))
              NE.:| [Query.Atom (Query.MkRel (Query.QVar 1) (PInner (Query.QVar 0)))]
          )
      binaryLiteralQuery =
        unaryChainQuery
          ( Query.Atom (Query.MkRel (Query.QVar 0) (PAdd (Query.QVar 1) (Query.QVar 2)))
              NE.:| [Query.Atom (Query.MkRel (Query.QVar 1) (PLit 0))]
          )
      fixedUnaryQuery =
        unaryChainQuery
          ( Query.Atom (Query.MkRel (Query.QVar 0) (POuter (Query.QVar 1)))
              NE.:| [Query.Atom (Query.MkRel (Query.QVar 1) (PInner (Query.EId 2)))]
          )
      headOnlyUnaryQuery =
        nestedQuery
          { Query.patQuery =
              Query.Conj $
                [9]
                  Query.::- ( Query.Atom (Query.MkRel (Query.QVar 0) (POuter (Query.QVar 1)))
                                NE.:| [Query.Atom (Query.MkRel (Query.QVar 1) (PInner (Query.QVar 2)))]
                            )
          }

      missingDb =
        Database.fromRelations
          [ Query.MkRel 100 (PAdd 10 20)
          , Query.MkRel 10 (PLit 0)
          ]
      missingCanonical = ematchDbWithCount nestedQuery missingDb
      missingPrepared =
        ematchPreparedDbWithCount (prepare nestedQuery) missingDb
   in PreparedTransposePin
        { nestedOrderExact =
            P.fst nestedCanonical P.== nestedExpected
              P.&& nestedPrepared P.== nestedCanonical
        , nestedRawSizeExact =
            P.snd nestedCanonical P.== 10
        , staticOrderExact =
            preparedStaticOrder (prepare nestedQuery)
              P.== preparedRuntimeOrder (prepare nestedQuery) nestedDb
              P.&& preparedStaticOrder (prepare nestedQuery) P.== Just [1, 2, 3, 0, 4]
        , atomCountEligibilityExact =
            P.not (preparedLayoutEligible (prepare oneAtomQuery))
              P.&& P.not (preparedLayoutEligible (prepare twoAtomQuery))
              P.&& preparedLayoutEligible (prepare threeAtomQuery)
              P.&& P.not (preparedLayoutEligible (prepare headOnlyQuery))
        , layoutValidationExact =
            Database.mkColumnLayout 3 [0, 1, 2]
              P.== Just (Database.identityColumnLayout 3)
              P.&& Database.mkColumnLayout 3 [0, 0, 2] P.== Nothing
              P.&& Database.mkColumnLayout 3 [0, 1] P.== Nothing
              P.&& Database.mkColumnLayout 3 [0, 1, 3] P.== Nothing
        , repeatedVariableExact =
            repeatedPrepared P.== repeatedCanonical
              P.&& P.length (P.fst repeatedCanonical) P.== 1
        , fixedColumnFallbackExact =
            fixedPrepared P.== fixedCanonical
        , identityLayoutExact =
            identityPrepared P.== identityCanonical
              P.&& P.length (P.fst identityCanonical) P.== 1
        , missingRelationExact =
            missingCanonical P.== ([], 0)
              P.&& missingPrepared P.== missingCanonical
        , unaryChainEligibilityExact =
            preparedLayoutEligible (prepare directedUnaryQuery)
              P.&& P.not (preparedLayoutEligible (prepare disconnectedUnaryQuery))
              P.&& P.not (preparedLayoutEligible (prepare repeatedUnaryQuery))
              P.&& P.not (preparedLayoutEligible (prepare sharedChildUnaryQuery))
              P.&& P.not (preparedLayoutEligible (prepare sharedRootUnaryQuery))
              P.&& P.not (preparedLayoutEligible (prepare cyclicUnaryQuery))
              P.&& P.not (preparedLayoutEligible (prepare binaryLiteralQuery))
              P.&& P.not (preparedLayoutEligible (prepare fixedUnaryQuery))
              P.&& P.not (preparedLayoutEligible (prepare headOnlyUnaryQuery))
        }

data PreparedDatabasePin = PreparedDatabasePin
  { fusedMatchesExact :: !P.Bool
  , preparedRowsExact :: !P.Bool
  , preparedOnlyCanonicalAbsent :: !P.Bool
  , preparedRequirementsExact :: !P.Bool
  , multipleLayoutsExact :: !P.Bool
  , absentPreparedFallbackExact :: !P.Bool
  , sameUnaryPreparedExact :: !P.Bool
  , distinctUnaryPreparedExact :: !P.Bool
  , unaryMissingFallbackExact :: !P.Bool
  }
  deriving (P.Eq, P.Show)

plannerLit :: Int -> Term PlannerLang
plannerLit i = wrapTerm (PLit i)

plannerNested :: Int -> Term PlannerLang
plannerNested i =
  wrapTerm $
    PAdd
      (plannerLit 0)
      (wrapTerm (PMul (plannerLit 1) (plannerLit i)))

mkPreparedDatabasePin ::
  Mut α (EGraph () PlannerLang) %1 ->
  BO α (Ur PreparedDatabasePin)
mkPreparedDatabasePin egraph = Control.do
  (Ur _, Ur _, egraph) <- addTerm (plannerNested 2) egraph
  (Ur _, Ur _, egraph) <- addTerm (plannerNested 3) egraph
  (Ur _, Ur _, egraph) <-
    addTerm
      (wrapTerm (POuter (wrapTerm (POuter (plannerLit 0)))))
      egraph
  (Ur _, Ur _, egraph) <-
    addTerm
      (wrapTerm (POuter (wrapTerm (POuter (plannerLit 1)))))
      egraph
  (Ur _, Ur _, egraph) <-
    addTerm
      (wrapTerm (POuter (wrapTerm (PInner (plannerLit 0)))))
      egraph
  (Ur _, Ur _, egraph) <-
    addTerm
      (wrapTerm (POuter (wrapTerm (PInner (plannerLit 1)))))
      egraph
  egraph <- rebuild egraph
  uncurry (flip lseq) Control.<$> sharing egraph \egraph -> Control.do
    let pattern =
          PNode $
            PAdd
              (PNode (PLit 0))
              (PNode (PMul (PNode (PLit 1)) (Metavar "x")))
        prepared = prepare (compile pattern)
        (canonicalOperators, preparedIndexes) =
          preparedDatabaseRequirements prepared
        canonicalSet = HS.fromList canonicalOperators
        preparedSet = HS.fromList preparedIndexes
        primaryKey = fromJust (listToMaybe preparedIndexes)
        preparedOperator = Database.preparedIndexOperator primaryKey
        layoutA = fromJust (Database.mkColumnLayout 3 [1, 2, 0])
        layoutB = fromJust (Database.mkColumnLayout 3 [2, 1, 0])
        keyA = fromJust (Database.mkPreparedIndexKey preparedOperator layoutA)
        keyB = fromJust (Database.mkPreparedIndexKey preparedOperator layoutB)
        multiLayoutSet = HS.fromList [keyA, keyB]
        unaryQuery outer inner =
          Query.PatternQuery
            { Query.root = 0
            , Query.varNames = V.empty
            , Query.patQuery =
                Query.Conj $
                  [0]
                    Query.::- ( Query.Atom (Query.MkRel (Query.QVar 0) (outer (Query.QVar 1)))
                                  NE.:| [Query.Atom (Query.MkRel (Query.QVar 1) (inner (Query.QVar 2)))]
                              )
            }
        sameUnaryQuery = unaryQuery POuter POuter
        distinctUnaryQuery = unaryQuery POuter PInner
        sameUnaryPrepared = prepare sameUnaryQuery
        distinctUnaryPrepared = prepare distinctUnaryQuery
        (sameCanonicalOperators, sameIndexes) =
          preparedDatabaseRequirements sameUnaryPrepared
        (distinctCanonicalOperators, distinctIndexes) =
          preparedDatabaseRequirements distinctUnaryPrepared
        distinctAllCanonical =
          HS.fromList (preparedOperators distinctUnaryPrepared)
    Ur full <- Database.buildDatabaseForPatterns False True egraph
    Ur fused <-
      Database.buildDatabaseForPrepared
        canonicalSet
        preparedSet
        True
        egraph
    Ur multiLayout <-
      Database.buildDatabaseForPrepared
        HS.empty
        multiLayoutSet
        True
        egraph
    Ur sameUnary <-
      Database.buildDatabaseForPrepared
        (HS.fromList sameCanonicalOperators)
        (HS.fromList sameIndexes)
        True
        egraph
    Ur distinctUnary <-
      Database.buildDatabaseForPrepared
        (HS.fromList distinctCanonicalOperators)
        (HS.fromList distinctIndexes)
        True
        egraph
    Ur missingUnary <-
      Database.buildDatabaseForPrepared
        distinctAllCanonical
        HS.empty
        True
        egraph
    let fusedMatchesExact =
          ematchPreparedDbWithCount prepared fused
            P.== ematchPreparedDbWithCount prepared full
        preparedRowsExact =
          P.all
            ( \key ->
                let operator = Database.preparedIndexOperator key
                    layout = Database.preparedIndexLayout key
                 in Database.getPreparedTrie key fused
                      P.== ( Trie.fromRows
                               P.<$> P.traverse
                                 (Database.permuteColumns layout)
                                 (Trie.toRows (Database.getTrie operator full))
                           )
            )
            preparedIndexes
        preparedOnlyCanonicalAbsent =
          P.all
            ( \key ->
                let operator = Database.preparedIndexOperator key
                 in HS.member operator canonicalSet
                      P.|| Database.getTrie operator fused P.== Trie.empty
            )
            preparedIndexes
        preparedRequirementsExact =
          P.length preparedIndexes P.== 1
            P.&& HS.size preparedSet P.== 1
            P.&& HS.size (HS.fromList (preparedIndexes P.<> preparedIndexes)) P.== 1
        multipleLayoutsExact =
          HS.size multiLayoutSet P.== 2
            P.&& Database.getTrie preparedOperator multiLayout P.== Trie.empty
            P.&& P.all
              ( \key ->
                  Database.getPreparedTrie key multiLayout
                    P.== ( Trie.fromRows
                             P.<$> P.traverse
                               (Database.permuteColumns (Database.preparedIndexLayout key))
                               (Trie.toRows (Database.getTrie preparedOperator full))
                         )
              )
              [keyA, keyB]
        emptyDatabase = Database.newDatabase
        absentPreparedFallbackExact =
          Database.getPreparedTrie primaryKey emptyDatabase P.== Nothing
            P.&& Database.getTrie preparedOperator emptyDatabase P.== Trie.empty
            P.&& ematchPreparedDbWithCount prepared emptyDatabase P.== ([], 0)
        sameCanonical =
          ematchDbWithCount sameUnaryQuery full
        samePrepared =
          ematchPreparedDbWithCount sameUnaryPrepared sameUnary
        sameOperator = Database.toOperator (POuter (0 :: EClassId))
        sameUnaryPreparedExact =
          preparedLayoutEligible sameUnaryPrepared
            P.&& HS.size (HS.fromList sameIndexes) P.== 1
            P.&& Database.getTrie sameOperator sameUnary P./= Trie.empty
            P.&& P.all
              (\key -> Database.getPreparedTrie key sameUnary P./= Nothing)
              sameIndexes
            P.&& P.not (P.null (P.fst sameCanonical))
            P.&& samePrepared P.== sameCanonical
        distinctCanonical =
          ematchDbWithCount distinctUnaryQuery full
        distinctPrepared =
          ematchPreparedDbWithCount distinctUnaryPrepared distinctUnary
        outerOperator = Database.toOperator (POuter (0 :: EClassId))
        innerOperator = Database.toOperator (PInner (0 :: EClassId))
        distinctUnaryPreparedExact =
          preparedLayoutEligible distinctUnaryPrepared
            P.&& HS.size (HS.fromList distinctIndexes) P.== 1
            P.&& Database.getTrie outerOperator distinctUnary P.== Trie.empty
            P.&& Database.getTrie innerOperator distinctUnary P./= Trie.empty
            P.&& P.all
              (\key -> Database.getPreparedTrie key distinctUnary P./= Nothing)
              distinctIndexes
            P.&& P.not (P.null (P.fst distinctCanonical))
            P.&& distinctPrepared P.== distinctCanonical
        unaryMissingFallbackExact =
          P.all
            (\key -> Database.getPreparedTrie key missingUnary P.== Nothing)
            distinctIndexes
            P.&& Database.getTrie outerOperator missingUnary P./= Trie.empty
            P.&& Database.getTrie innerOperator missingUnary P./= Trie.empty
            P.&& ematchPreparedDbWithCount distinctUnaryPrepared missingUnary
              P.== distinctCanonical
            P.&& P.not (P.null (P.fst distinctCanonical))
    Control.pure $
      Ur
        PreparedDatabasePin
          { fusedMatchesExact
          , preparedRowsExact
          , preparedOnlyCanonicalAbsent
          , preparedRequirementsExact
          , multipleLayoutsExact
          , absentPreparedFallbackExact
          , sameUnaryPreparedExact
          , distinctUnaryPreparedExact
          , unaryMissingFallbackExact
          }

mkMixedSelectAllSaturationPin ::
  Mut α (EGraph () PlannerLang) %1 ->
  BO α (Ur (Maybe P.Bool))
mkMixedSelectAllSaturationPin egraph = Control.do
  (Ur _, Ur leaf, egraph) <- addTerm (plannerLit 2) egraph
  (Ur _, Ur root, egraph) <- addTerm (plannerNested 2) egraph
  let nestedPattern =
        PNode $
          PAdd
            (PNode (PLit 0))
            (PNode (PMul (PNode (PLit 1)) (Metavar "x")))
      ruleDefs =
        [ (Metavar "z" Saturation.==> Metavar "z")
            { Saturation.name = "select-all-noop"
            }
        , (nestedPattern Saturation.==> Metavar "x")
            { Saturation.name = "nested-collapse"
            }
        ]
      compiledRules =
        case P.traverse Saturation.compileRule ruleDefs of
          Left err -> P.error (P.show err)
          Right compiled -> compiled
  egraph <-
    Saturation.saturate
      Saturation.defaultConfig
        { Saturation.maxIterations = Just 2
        , Saturation.nodeLimit = Nothing
        , Saturation.scheduler = Nothing
        }
      compiledRules
      egraph
  uncurry (flip lseq) Control.<$> sharing egraph \egraph ->
    equivalent egraph root leaf

intT :: Int -> Term Lang1
intT i = wrapTerm $ I i

mkCase1 :: Int -> Mut α (EGraph () Lang1) %1 -> BO α (Ur [(EClassId, Substitution String)])
mkCase1 n egraph = Control.do
  (ns, egraph) <- forReborrowing egraph (NE.fromList [1 .. n]) \egraph i ->
    move i & \(Ur i) -> Control.do
      (Ur _, eid, egraph) <- addTerm (intT i) egraph
      Control.pure $ egraph `lseq` eid
  Ur ns <- Control.pure $ move ns
  (gs, egraph) <- forReborrowing egraph ns \egraph (Ur eid) -> Control.do
    (Ur geid, egraph) <- addNode egraph $ ENode $ G eid
    Control.pure $ egraph `lseq` Ur (fromJust geid)
  Ur gs <- Control.pure $ move gs
  (Ur _, egraph) <- merges (unur Data.<$> gs) egraph
  let fs = NE.zipWith (\(Ur nid) (Ur gid) -> ENode $ F nid gid) ns gs
  (fs, egraph) <- forReborrowing egraph fs \egraph node ->
    move node & \(Ur node) -> Control.do
      (Ur feid, egraph) <- addNode egraph node
      Control.pure $ egraph `lseq` fromJust feid
  Ur fs <- Control.pure $ move fs
  (Ur _, egraph) <- merges fs egraph
  egraph <- rebuild egraph
  uncurry (flip lseq) Control.<$> sharing egraph do
    ematch (PNode $ F (Metavar "a") $ PNode $ G (Metavar "a"))

{- | B12 pinning: nested two-atom pattern @G (G x)@ — exactly one match per
congruence-distinct chain; the internal PNode variable never multiplies
matches on a canonical database.
-}
mkNestedPin :: Mut α (EGraph () Lang1) %1 -> BO α (Ur [(EClassId, Substitution String)])
mkNestedPin egraph = Control.do
  (Ur _, Ur _aid, egraph) <- addTerm (wrapTerm (G (wrapTerm (G (intT 1))))) egraph
  egraph <- rebuild egraph
  uncurry (flip lseq) Control.<$> sharing egraph do
    ematch (PNode $ G $ PNode $ G (Metavar "x"))

{- | B12 pinning: SelectAll (bare metavar) yields one match per CLASS even
when a class spans multiple operators (selectAll keeps cross-operator
multiplicity; the match dedup collapses it).
-}
mkSelectAllPin :: Mut α (EGraph () Lang1) %1 -> BO α (Ur [(EClassId, Substitution String)])
mkSelectAllPin egraph = Control.do
  (Ur _, Ur iid, egraph) <- addTerm (intT 1) egraph
  (Ur mgid, egraph) <- addNode egraph (ENode (G iid))
  (Ur _, egraph) <- merge (fromJust mgid) iid egraph
  egraph <- rebuild egraph
  uncurry (flip lseq) Control.<$> sharing egraph do
    ematch (Metavar "a")

data DatabaseFilterPin = DatabaseFilterPin
  { selectedLiteralEqual :: !P.Bool
  , selectedUnaryEqual :: !P.Bool
  , excludedLiteralEmpty :: !P.Bool
  , excludedBinaryEmpty :: !P.Bool
  , emptySelectionEmpty :: !P.Bool
  , auxiliaryIndexesEmpty :: !P.Bool
  , preparedMatchesEqual :: !P.Bool
  , preparedCanonicalizationEqual :: !P.Bool
  }
  deriving (P.Eq, P.Show)

data MixedSelectAllPin = MixedSelectAllPin
  { selectAllOrderExact :: !P.Bool
  , selectAllMatchesExact :: !P.Bool
  , selectAllRawSizeExact :: !P.Bool
  , ordinaryMatchesExact :: !P.Bool
  , ordinaryRawSizeExact :: !P.Bool
  }
  deriving (P.Eq, P.Show)

{- | Differential pin for the operator-filtered database builder.

The merge leaves the child stored in the @G@ node noncanonical unless the
caller requests a rebuild. Running both modes locks the invariant that
filtering on the raw node is sound while row values still follow the normal
canonicalization path.
-}
mkDatabaseFilterPin ::
  P.Bool ->
  Mut α (EGraph () Lang1) %1 ->
  BO α (Ur DatabaseFilterPin)
mkDatabaseFilterPin assumeCanonical egraph = Control.do
  (Ur _, Ur i1, egraph) <- addTerm (intT 1) egraph
  (Ur _, Ur i2, egraph) <- addTerm (intT 2) egraph
  (Ur _, egraph) <- addNode egraph (ENode (G i1))
  (Ur _, egraph) <- addNode egraph (ENode (F i1 i2))
  (Ur _, egraph) <- merge i1 i2 egraph
  egraph <-
    if assumeCanonical
      then rebuild egraph
      else Control.pure egraph
  uncurry (flip lseq) Control.<$> sharing egraph \egraph -> Control.do
    let opI1 = Database.toOperator (I 1 :: Lang1 EClassId)
        opI2 = Database.toOperator (I 2 :: Lang1 EClassId)
        opG = Database.toOperator (G i1)
        opF = Database.toOperator (F i1 i2)
        required = HS.fromList [opI1, opG]
        pat = PNode (G (Metavar "x")) :: Pattern Lang1 P.String
        prepared = prepare (compile pat)
        preparedLayout = fromJust (Database.mkColumnLayout 3 [1, 2, 0])
        preparedKey = fromJust (Database.mkPreparedIndexKey opF preparedLayout)
    Ur full <- Database.buildDatabaseForPatterns False assumeCanonical egraph
    Ur filtered <- Database.buildDatabaseForOperators required assumeCanonical egraph
    Ur empty <- Database.buildDatabaseForOperators HS.empty assumeCanonical egraph
    Ur fused <-
      Database.buildDatabaseForPrepared
        HS.empty
        (HS.singleton preparedKey)
        assumeCanonical
        egraph
    let selectedLiteralEqual =
          Database.getTrie opI1 filtered P.== Database.getTrie opI1 full
        selectedUnaryEqual =
          Database.getTrie opG filtered P.== Database.getTrie opG full
        excludedLiteralEmpty = Database.getTrie opI2 filtered P.== Trie.empty
        excludedBinaryEmpty = Database.getTrie opF filtered P.== Trie.empty
        emptySelectionEmpty =
          P.all
            (\op -> Database.getTrie op empty P.== Trie.empty)
            [opI1, opI2, opG, opF]
        auxiliaryIndexesEmpty =
          IS.null (Database.universe filtered)
            P.&& P.null (Database.selectAll filtered)
        preparedMatchesEqual =
          ematchPreparedDbWithCount prepared filtered
            P.== ematchPreparedDbWithCount prepared full
        preparedCanonicalizationEqual =
          Database.getTrie opF fused P.== Trie.empty
            P.&& Database.getPreparedTrie preparedKey fused
              P.== ( Trie.fromRows
                       P.<$> P.traverse
                         (Database.permuteColumns preparedLayout)
                         (Trie.toRows (Database.getTrie opF full))
                   )
    Control.pure $
      Ur
        DatabaseFilterPin
          { selectedLiteralEqual
          , selectedUnaryEqual
          , excludedLiteralEmpty
          , excludedBinaryEmpty
          , emptySelectionEmpty
          , auxiliaryIndexesEmpty
          , preparedMatchesEqual
          , preparedCanonicalizationEqual
          }

{- | A full database must retain cross-operator multiplicity for a SelectAll
rule even when ordinary rules are present. The two roots of the merged class
come from its @G@ and @I 1@ operators, followed by the distinct @I 2@ class.
-}
mkMixedSelectAllPin ::
  Mut α (EGraph () Lang1) %1 ->
  BO α (Ur MixedSelectAllPin)
mkMixedSelectAllPin egraph = Control.do
  (Ur _, Ur i1, egraph) <- addTerm (intT 1) egraph
  (Ur _, Ur i2, egraph) <- addTerm (intT 2) egraph
  (Ur mg, egraph) <- addNode egraph (ENode (G i1))
  (Ur _, egraph) <- merge (fromJust mg) i1 egraph
  egraph <- rebuild egraph
  uncurry (flip lseq) Control.<$> sharing egraph \egraph -> Control.do
    Ur root1 <- unsafeFind egraph i1
    Ur root2 <- unsafeFind egraph i2
    Ur db <- Database.buildDatabaseForPatterns True True egraph
    let selectPrepared =
          prepare (compile (Metavar "x" :: Pattern Lang1 P.String))
        ordinaryPrepared =
          prepare (compile (PNode (G (Metavar "x")) :: Pattern Lang1 P.String))
        (selectMatches, selectRawSize) =
          ematchPreparedDbWithCount selectPrepared db
        (ordinaryMatches, ordinaryRawSize) =
          ematchPreparedDbWithCount ordinaryPrepared db
    Control.pure $
      Ur
        MixedSelectAllPin
          { selectAllOrderExact =
              Database.selectAll db P.== [root1, root1, root2]
          , selectAllMatchesExact =
              P.map P.fst selectMatches P.== [root1, root2]
          , selectAllRawSizeExact = selectRawSize P.== 3
          , ordinaryMatchesExact =
              P.map P.fst ordinaryMatches P.== [root1]
          , ordinaryRawSizeExact = ordinaryRawSize P.== 2
          }
