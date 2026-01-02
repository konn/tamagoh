{-# LANGUAGE TypeFamilies #-}

module Language.Egglog.Core where

import Data.EGraph.Types.EClassId (EClassId)
import Data.Functor.Combinator
import Data.Functor.Const (Const)
import Data.HFunctor.HTraversable
import Data.Kind (Type)
import GHC.Generics (Generic, Generic1)

newtype HFix f a = HFix {unHFix :: f (HFix f) a}

wrapFix1 :: f (HFix f) a -> HFix f a
wrapFix1 = HFix

unwrapFix1 :: HFix f a -> f (HFix f) a
unwrapFix1 = unHFix

foldFix1 :: (HFunctor f) => (forall x. f r x -> r x) -> HFix f a -> r a
foldFix1 f (HFix t) = f (hmap (foldFix1 f) t)

unfoldFix1 ::
  (HFunctor f) =>
  (forall x. r x -> f r x) ->
  r a ->
  HFix f a
unfoldFix1 f r = HFix $ (hmap $ unfoldFix1 f) $ f r

type HSum ::
  forall k k1.
  ((k -> Type) -> k1 -> Type) ->
  ((k -> Type) -> k1 -> Type) ->
  (k -> Type) ->
  k1 ->
  Type
data HSum t u f a = HInL (t f a) | HInR (u f a)
  deriving (Show, Eq, Ord, Generic1, Generic, Functor, Foldable, Traversable)

instance (HFunctor t, HFunctor u) => HFunctor (HSum t u) where
  hmap f (HInL x) = HInL (hmap f x)
  hmap f (HInR y) = HInR (hmap f y)

instance (HTraversable t, HTraversable u) => HTraversable (HSum t u) where
  htraverse f (HInL x) = HInL <$> htraverse f x
  htraverse f (HInR y) = HInR <$> htraverse f y

type Pattern :: ((k -> Type) -> k -> Type) -> Type -> k -> Type
type Pattern f v a = HFix (HSum (ConstF v) f) a

data ArithExpr f a where
  Var :: String -> ArithExpr f a
  Lit :: Int -> ArithExpr f Int
  Add :: f Int -> f Int -> ArithExpr f Int
  Mul :: f Int -> f Int -> ArithExpr f Int

instance HFunctor ArithExpr where
  hmap = hmapDefault

instance HTraversable ArithExpr where
  htraverse _ (Var s) = pure $ Var s
  htraverse _ (Lit n) = pure $ Lit n
  htraverse f (Add x y) = Add <$> f x <*> f y
  htraverse f (Mul x y) = Mul <$> f x <*> f y

newtype HENode l a = HENode (l (Const EClassId) a)
