{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Data.HashMap.Mutable.Linear.Borrowed.Internal (
  module Data.HashMap.Mutable.Linear.Borrowed.Internal,
) where

import Control.Monad.Borrow.Pure.Utils (deepCloneArray')
import Control.Syntax.DataFlow qualified as DataFlow
import Data.HashMap.Mutable.Linear qualified as Raw
import Data.HashMap.Mutable.Linear.Internal qualified as Raw
import Prelude.Linear hiding (filter, insert, lookup, mapMaybe, take)
import Unsafe.Linear qualified as Unsafe

deepCloneHashMap :: (Dupable k, Dupable v) => Raw.HashMap k v %1 -> (Raw.HashMap k v, Raw.HashMap k v)
deepCloneHashMap (Raw.HashMap !i !j !robinArr) = DataFlow.do
  (robinArr, !robinArr2) <- deepCloneArray' dupRobinVal robinArr
  (Raw.HashMap i j robinArr, Raw.HashMap i j robinArr2)

dupRobinVal ::
  (Dupable k, Dupable v) =>
  Maybe (Raw.RobinVal k v) %1 ->
  (Maybe (Raw.RobinVal k v), Maybe (Raw.RobinVal k v))
dupRobinVal = Unsafe.toLinear \case
  Nothing -> (Nothing, Nothing)
  Just (Raw.RobinVal (Raw.PSL i) !k !v) -> DataFlow.do
    !i' <- Unsafe.toLinear (\(_, !x) -> x) $ dup i
    !k' <- Unsafe.toLinear (\(_, !x) -> x) $ dup k
    !v' <- Unsafe.toLinear (\(_, !x) -> x) $ dup v
    (Just (Raw.RobinVal (Raw.PSL i) k v), Just (Raw.RobinVal (Raw.PSL i') k' v'))
