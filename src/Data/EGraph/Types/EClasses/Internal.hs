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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.EGraph.Types.EClasses.Internal (
  module Data.EGraph.Types.EClasses.Internal,
) where

import Control.Monad.Borrow.Pure
import Data.EGraph.Types.EClassId
import Data.EGraph.Types.ENode
import Data.Functor.Classes (Show1)
import Data.HashMap.Mutable.Linear.Borrowed (HashMap)
import Data.HashMap.Mutable.Linear.Borrowed qualified as HMB
import Data.Set.Mutable.Linear.Borrowed (Set)
import Data.Unrestricted.Linear.Lifted (Copyable1)
import GHC.Generics qualified as GHC
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear
import Prelude.Linear.Internal.Generically
import Text.Show.Borrowed

newtype EClasses d l = EClasses (Raw d l)
  deriving newtype (Consumable)

type Raw d l = HashMap EClassId (EClass d l)

new :: Linearly %1 -> EClasses d l
new = EClasses . HMB.empty 16

-- TODO: use (unsafe) indirection around Sets to reduce copying cost
data EClass d l
  = EClass
  { nodes :: {-# UNPACK #-} !(Set (ENode l))
  , parents :: {-# UNPACK #-} !(HashMap (ENode l) EClassId)
  , analysis :: !(Ref d)
  }
  deriving (GHC.Generic)

deriveGeneric ''EClass

deriving via Generically (EClass d l) instance (Consumable d) => Consumable (EClass d l)

deriving via Generically (EClass d l) instance (Dupable d) => Dupable (EClass d l)

deriving via Generically (EClass d l) instance (Copyable1 l, Show1 l, Display d) => Display (EClass d l)

deriving newtype instance (Dupable d) => Dupable (EClasses d l)

deriving via Raw d l instance (Copyable1 l, Show1 l, Display d) => Display (EClasses d l)
