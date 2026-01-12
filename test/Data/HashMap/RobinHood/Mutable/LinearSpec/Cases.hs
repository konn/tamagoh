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

module Data.HashMap.RobinHood.Mutable.LinearSpec.Cases (
  module Data.HashMap.RobinHood.Mutable.LinearSpec.Cases,
) where

import Control.Monad.Borrow.Pure (linearly)
import Data.HashMap.RobinHood.Mutable.Linear as HM
import Prelude.Linear hiding (lookup)
import Prelude qualified as P

withNewEmptyHashMap :: (HashMap k v %1 -> Ur r) %1 -> Ur r
withNewEmptyHashMap f = linearly $ f . new 1

data Case1Result = Case1Result
  { initOneResident :: Maybe Int
  , newOneResident :: Maybe Int
  , initTwoResident :: Maybe Int
  , deltedOneResident :: Maybe Int
  , finalResult :: [(String, Int)]
  }
  deriving (Show, P.Eq, P.Ord)

case1 :: HashMap String Int %1 -> Ur Case1Result
case1 hm =
  HM.insert "One" 1 hm & \(Ur initOneResident, hm) ->
    HM.lookup "One" hm & \(Ur newOneResident, hm) ->
      HM.insert "Two" 2 hm & \(Ur initTwoResident, hm) ->
        HM.delete "One" hm & \(Ur deltedOneResident, hm) ->
          HM.toList hm & \(Ur finalResult) ->
            Ur Case1Result {..}
