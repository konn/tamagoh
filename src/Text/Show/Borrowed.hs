{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}

module Text.Show.Borrowed (
  Display (..),
  display,
  AsCopyableShow (..),
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Control.Monad.Borrow.Pure.Internal
import Data.Functor.Linear qualified as Data
import Data.Int
import Data.List.Linear qualified as List
import Data.Unrestricted.Linear qualified as Ur
import Data.Word
import GHC.Exts (Any)
import Generics.Linear qualified as GLC
import Prelude.Linear
import Prelude.Linear.Generically qualified as GLC
import Prelude qualified as P

class Display a where
  displayPrec :: Int -> Share α a -> BO α (Ur ShowS)

display :: (Display a) => Share α a -> BO α (Ur String)
display bor = Control.do
  Ur shown <- displayPrec 0 bor
  Control.pure $ Ur $ shown ""

newtype AsCopyableShow a = AsCopyableShow {runAsCopyableShow :: a}
  deriving newtype (Copyable, Show)

instance (Copyable a, Show a) => Display (AsCopyableShow a) where
  displayPrec d bor = Control.pure $ Ur $ showsPrec d (copy bor)

deriving via AsCopyableShow Double instance Display Double

deriving via AsCopyableShow Float instance Display Float

deriving via AsCopyableShow Bool instance Display Bool

deriving via AsCopyableShow Int instance Display Int

deriving via AsCopyableShow Int8 instance Display Int8

deriving via AsCopyableShow Int16 instance Display Int16

deriving via AsCopyableShow Int32 instance Display Int32

deriving via AsCopyableShow Int64 instance Display Int64

deriving via AsCopyableShow Word instance Display Word

deriving via AsCopyableShow Word8 instance Display Word8

deriving via AsCopyableShow Word16 instance Display Word16

deriving via AsCopyableShow Word32 instance Display Word32

deriving via AsCopyableShow Word64 instance Display Word64

instance (Display a) => Display (Maybe a) where
  displayPrec d bor = Control.do
    case split bor of
      Nothing -> Control.pure $ Ur $ showString "Nothing"
      Just bor -> Control.do
        Ur shown <- displayPrec 11 bor
        Control.pure $ Ur $ showParen (d > 10) $ showString "Just " P.. shown

instance {-# OVERLAPPABLE #-} (Display a) => Display [a] where
  displayPrec _ as = Control.do
    as <- Data.mapM (\a -> move a & \(Ur a) -> displayPrec 0 a) $ split as
    let %1 !(Ur showns) =
          foldr (Ur.lift2 (P..)) (Ur P.id)
            $ List.intersperse (Ur $ showString ", ") as
    Control.pure $ Ur $ showString "[" P.. showns P.. showString "]"

instance {-# OVERLAPPING #-} Display String where
  displayPrec _ bor = Control.pure $ Ur $ showString (copy bor)
  {-# INLINE displayPrec #-}

instance (Display a, Display b) => Display (a, b) where
  displayPrec _ bor = Control.do
    let (borA, borB) = splitPair bor
    Ur shownA <- displayPrec 0 borA
    Ur shownB <- displayPrec 0 borB
    Control.pure
      $ Ur
      $ showString "("
      P.. shownA
      P.. showString ", "
      P.. shownB
      P.. showString ")"

instance (Display a, Display b) => Display (Either a b) where
  displayPrec d bor = Control.do
    case splitEither bor of
      Left borA -> Control.do
        Ur shownA <- displayPrec 11 borA
        Control.pure
          $ Ur
          $ showParen (d > 10)
          $ showString "Left "
          P.. shownA
      Right borB -> Control.do
        Ur shownB <- displayPrec 11 borB
        Control.pure
          $ Ur
          $ showParen (d > 10)
          $ showString "Right "
          P.. shownB

type GenericDisplay a = (GLC.Generic a, GDisplay (GLC.Rep a))

instance (GenericDisplay a) => Display (GLC.Generically a) where
  displayPrec d (UnsafeAlias bor) = Control.do
    let repBor = UnsafeAlias $ GLC.from $ GLC.unGenerically bor
    Ur shown <- gdisplayPrec Unnamed d repBor
    Control.pure $ Ur shown

data FieldTy = Named | Unnamed

class GDisplay f where
  gdisplayPrec :: FieldTy -> Int -> Share α (f p) -> BO α (Ur ShowS)

instance GDisplay GLC.U1 where
  gdisplayPrec _ _ _ = Control.pure $ Ur P.id

instance (GDisplay f, GDisplay g) => GDisplay (f GLC.:*: g) where
  gdisplayPrec ty d bor = Control.do
    let UnsafeAlias (!borF GLC.:*: !borG) = bor
    Ur shownF <- gdisplayPrec ty d $ UnsafeAlias borF
    Ur shownG <- gdisplayPrec ty d $ UnsafeAlias borG
    let sep = case ty of
          Named -> showString ", "
          Unnamed -> showString " "
    Control.pure $ Ur $ shownF P.. sep P.. shownG

instance (GDisplay f, GDisplay g) => GDisplay (f GLC.:+: g) where
  gdisplayPrec ty d bor = Control.do
    case bor of
      UnsafeAlias (GLC.L1 borF) -> gdisplayPrec ty d $ UnsafeAlias borF
      UnsafeAlias (GLC.R1 borG) -> gdisplayPrec ty d $ UnsafeAlias borG

instance (GDisplay f) => GDisplay (GLC.D1 d f) where
  gdisplayPrec ty d bor = Control.do
    let UnsafeAlias (GLC.M1 borF) = bor
    gdisplayPrec ty d $ UnsafeAlias borF

instance (GLC.Constructor c, GDisplay f) => GDisplay (GLC.C1 c f) where
  gdisplayPrec _ d bor = Control.do
    let conName = GLC.conName (undefined :: GLC.C1 c f GHC.Exts.Any)
        UnsafeAlias (GLC.M1 borF) = bor
        ty =
          if GLC.conIsRecord (undefined :: GLC.C1 c f GHC.Exts.Any)
            then Named
            else Unnamed
    Ur shownF <- gdisplayPrec ty d $ UnsafeAlias borF
    case ty of
      Named -> Control.pure $ Ur $ showString conName P.. showString " { " P.. shownF P.. showString " }"
      Unnamed ->
        Control.pure
          $ Ur
          $ showParen (d > 10)
          $ showString conName
          P.. showString " "
          P.. shownF

instance (GLC.Selector s, GDisplay f) => GDisplay (GLC.S1 s f) where
  gdisplayPrec ty d bor = Control.do
    let fld = GLC.selName (undefined :: GLC.S1 s f GHC.Exts.Any)
        UnsafeAlias (GLC.M1 borF) = bor
    Ur shown <- gdisplayPrec ty d $ UnsafeAlias borF
    if null fld
      then Control.pure $ Ur $ showParen (d > 10) shown
      else Control.pure $ Ur $ showString fld P.. showString " = " P.. shown

instance (Display c) => GDisplay (GLC.K1 i c) where
  gdisplayPrec _ d bor = Control.do
    let UnsafeAlias (GLC.K1 c) = bor
    displayPrec d (UnsafeAlias c)
