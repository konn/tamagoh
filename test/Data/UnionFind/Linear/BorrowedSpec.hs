{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.UnionFind.Linear.BorrowedSpec (
  module Data.UnionFind.Linear.BorrowedSpec,
) where

import Control.Functor.Linear qualified as Control
import Control.Monad.Borrow.Pure
import Data.Functor.Linear qualified as Data
import Data.Maybe (isJust)
import Data.UnionFind.Linear.Borrowed
import Prelude.Linear (Ur (..), dup, lseq, move, unur)
import Prelude.Linear qualified as PL
import Test.Tasty
import Test.Tasty.HUnit

test_union :: TestTree
test_union =
  testGroup
    "union"
    [ testCase "disjoint" do
        let Ur (bothJust, noneq) = linearly \l ->
              dup l PL.& \(l, l') ->
                runBO l Control.do
                  let %1 !(uf, lend) = new 10 l'
                  (Ur key1, uf) <- fresh uf
                  (Ur key2, uf) <- fresh uf
                  (Ur eql, uf) <- sharing uf \uf -> Control.do
                    Ur k1 <- move Control.<$> find key1 uf
                    Ur k2 <- move Control.<$> find key2 uf
                    Control.pure PL.$ move (isJust k1 && isJust k2, k1 PL./= k2)
                  Control.pure PL.$ \end ->
                    uf `lseq` reclaim lend end `lseq` eql
        assertBool "BothJust" bothJust
        assertBool "Nonequal" noneq
    , testCase "two unioned" do
        let Ur (key1, key2, newKey, k1, k2) = linearly \l ->
              dup l PL.& \(l, l') ->
                runBO l Control.do
                  let %1 !(uf, lend) = new 10 l'
                  (Ur key1, uf) <- fresh uf
                  (Ur key2, uf) <- fresh uf
                  (Ur newKey, uf) <- union key1 key2 uf
                  ((k1, k2), uf) <- sharing uf \uf -> Control.do
                    k1 <- Data.fmap unur Control.<$> find key1 uf
                    k2 <- Data.fmap unur Control.<$> find key2 uf
                    Control.pure (k1, k2)
                  Control.pure PL.$ \end ->
                    uf `lseq` reclaim lend end `lseq` (key1, key2, newKey, k1, k2)
        assertBool "newKey is no Nohing!" $ isJust newKey
        Just newKey <- pure $ newKey
        assertBool "newKey must be one of original keys" $
          key1 == newKey || key2 == newKey
        Just newKey @=? k1
        Just newKey @=? k2
    , testCase "two equal, one indep" do
        let Ur ((key1, key2, key3), newKey, k1, k2, k3) = linearly \l ->
              dup l PL.& \(l, l') ->
                runBO l Control.do
                  let %1 !(uf, lend) = new 10 l'
                  (Ur key1, uf) <- fresh uf
                  (Ur key2, uf) <- fresh uf
                  (Ur key3, uf) <- fresh uf
                  (Ur newKey, uf) <- union key1 key2 uf
                  ((k1, k2, k3), uf) <- sharing uf \uf -> Control.do
                    k1 <- Data.fmap unur Control.<$> find key1 uf
                    k2 <- Data.fmap unur Control.<$> find key2 uf
                    k3 <- Data.fmap unur Control.<$> find key3 uf
                    Control.pure (k1, k2, k3)
                  Control.pure PL.$ \end ->
                    uf `lseq` reclaim lend end `lseq` ((key1, key2, key3), newKey, k1, k2, k3)
        assertBool "newKey is no Nohing!" $ isJust newKey
        Just newKey <- pure $ newKey
        assertBool "newKey must be one of original keys" $
          key1 == newKey || key2 == newKey
        Just newKey @=? k1
        Just newKey @=? k2
        k3 @?= Just key3
        newKey /= key3 @? "k1, k2 must be different from k3"
    ]
