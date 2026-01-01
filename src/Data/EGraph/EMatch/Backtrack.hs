{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | A sub-optimal, simple backtracking E-matching algorithm.
module Data.EGraph.EMatch.Backtrack (ematchBacktrack) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.EGraph.EMatch.Types
import Data.EGraph.Types
import Data.Foldable hiding (find)
import Data.Hashable (Hashable)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (catMaybes, maybeToList)
import Data.Unrestricted.Linear (Ur (..), UrT (..), runUrT)
import Data.Unrestricted.Linear.Lifted (Movable1)
import Prelude.Linear ()
import Prelude as P

ematchBacktrack ::
  forall l v α.
  (Movable1 l, Matchable l, Hashable v) =>
  Share α (EGraph l) ->
  Pattern l v ->
  EClassId ->
  BO α (Ur [Substitution v])
ematchBacktrack egraph = go [mempty]
  where
    go ::
      [Substitution v] ->
      Pattern l v ->
      EClassId ->
      BO α (Ur [Substitution v])
    go subss pat eid =
      find egraph eid Control.>>= \case
        Ur Nothing -> Control.pure (Ur [])
        Ur (Just eid) -> runUrT do
          case pat of
            Metavar v ->
              catMaybes
                <$> mapM
                  ( \sub ->
                      case lookupVar v sub of
                        Just eid' -> do
                          eq <- UrT $ equivalent egraph eid eid'
                          if eq == Just True
                            then pure $ Just sub
                            else pure Nothing
                        Nothing -> pure $ Just $ insertVar v eid sub
                  )
                  subss
            PNode p -> do
              may <- UrT $ lookupEClass eid egraph
              case may of
                Nothing -> pure []
                Just nodes -> do
                  let matches =
                        [ m
                        | ENode n <- NE.toList nodes
                        , m <- maybeToList (tryMatch p n)
                        ]
                  concat
                    <$> mapM
                      ( foldlM
                          (\subss -> UrT . uncurry (go subss))
                          subss
                      )
                      matches
