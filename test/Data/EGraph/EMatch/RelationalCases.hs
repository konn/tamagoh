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
import Data.EGraph.EMatch.Types
import Data.EGraph.Types
import Data.EGraph.Types.Language (deriveLanguage)
import Data.Functor.Linear qualified as Data
import Data.HashSet qualified as HS
import Data.IntSet qualified as IS
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromJust)
import Data.Trie qualified as Trie
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
    Ur full <- Database.buildDatabaseForPatterns False assumeCanonical egraph
    Ur filtered <- Database.buildDatabaseForOperators required assumeCanonical egraph
    Ur empty <- Database.buildDatabaseForOperators HS.empty assumeCanonical egraph
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
