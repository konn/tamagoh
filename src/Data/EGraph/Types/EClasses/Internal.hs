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
import Data.HashSet (HashSet)
import Data.Ref.Linear.Borrow (Ref)
import GHC.Generics qualified as GHC
import Generics.Linear.TH (deriveGeneric)
import Prelude.Linear
import Prelude.Linear.Internal.Generically
import Text.Show.Borrowed

newtype EClasses d l = EClasses (Raw d l)
  deriving newtype (Consumable)

type Raw d l = HashMap EClassId (EClass d l)

new :: Linearly %1 -> EClasses d l
new = EClasses . HMB.empty 2048

{- | Hegg's SizedList: cached length plus the newest-first,
duplicate-preserving parent sequence. Entries are stored in worklist
orientation @(owner class, parent node)@ so merge and analysis repair can
enqueue them without any per-element rewrapping. The strict constructor
(not a lazy pair) is essential: 'Data.Ref.Linear.Borrow.Ref' updates force
only to WHNF, and 'Parents'' strict count field keeps the length from
accumulating a thunk chain across merge storms.
-}
data Parents l = Parents {-# UNPACK #-} !Int ![Ur (EClassId, ENode l)]

data EClass d l
  = EClass
  { nodes :: !(Ref (Ur (HashSet (ENode l))))
  , parents :: !(Ref (Parents l))
  -- ^ Sized parent history in worklist orientation; see 'Parents'.
  , analysis :: !(Ref d)
  }
  deriving (GHC.Generic)

deriveGeneric ''Parents

deriveGeneric ''EClass

deriving via
  Generically (Parents l)
  instance
    Consumable (Parents l)

deriving via
  Generically (Parents l)
  instance
    Dupable (Parents l)

deriving via
  Generically (Parents l)
  instance
    Movable (Parents l)

deriving via
  Generically (Parents l)
  instance
    (Show1 l) => Display (Parents l)

deriving anyclass instance (Dupable d) => Clone (EClass d l)

deriving via
  Generically (EClass d l)
  instance
    (Consumable d) => Consumable (EClass d l)

deriving via
  Generically (EClass d l)
  instance
    (Dupable d) => Dupable (EClass d l)

deriving via
  Generically (EClass d l)
  instance
    (Show1 l, Display d) => Display (EClass d l)

deriving newtype instance (Dupable d) => Dupable (EClasses d l)

deriving via
  Raw d l
  instance
    (Show1 l, Display d) =>
    Display (EClasses d l)
