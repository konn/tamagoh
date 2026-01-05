{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Tamagoh.Bench.Math (
  module Tamagoh.Bench.Math,
) where

import Algebra.Semilattice
import Control.Arrow ((>>>))
import Control.DeepSeq (NFData, NFData1)
import Control.Functor.Linear qualified as Control
import Control.Lens (view, (^.), _1, _2)
import Control.Lens.Lens (Lens')
import Control.Monad.Borrow.Pure (Copyable, (<$~))
import Data.Coerce (coerce)
import Data.EGraph.Immutable qualified as Tamagoh
import Data.EGraph.Saturation (MatchInfo (..))
import Data.EGraph.Types.EGraph qualified as Raw
import Data.EGraph.Types.Language (deriveLanguage)
import Data.Equality.Analysis qualified as Hegg
import Data.Equality.Extraction qualified as Hegg
import Data.Equality.Graph qualified as Hegg
import Data.Equality.Graph.Lens qualified as Hegg
import Data.Equality.Matching qualified as Hegg
import Data.Equality.Matching.Database qualified as Hegg
import Data.Equality.Saturation qualified as Hegg
import Data.Foldable1 (foldl1')
import Data.Functor.Foldable
import Data.HashMap.Strict qualified as HM
import Data.Hashable (Hashable)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromJust, isJust)
import Data.Semigroup qualified as Semi
import Data.Unrestricted.Linear (Consumable, Dupable, Movable, Ur (..), consume)
import GHC.Generics qualified as GHC
import Tamagoh.Bench.Orphans ()
import Text.Show.Borrowed (Display)
import Prelude as P

data Math v
  = Diff v v
  | Integral v v
  | v :+ v
  | v :- v
  | v :* v
  | v :/ v
  | v :^ v
  | Ln v
  | Sqrt v
  | Sin v
  | Cos v
  | Const Double
  | Var String
  deriving (Show, Eq, Ord, GHC.Generic, GHC.Generic1)
  deriving anyclass (NFData1, NFData)

deriveLanguage ''Math

diff :: (Corecursive math, Base math ~ Math) => math -> math -> math
diff x y = embed (Diff x y)
{-# INLINE diff #-}
{-# SPECIALIZE INLINE diff :: Tamagoh.Term Math -> Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE diff :: Hegg.Fix Math -> Hegg.Fix Math -> Hegg.Fix Math #-}

integral :: (Corecursive math, Base math ~ Math) => math -> math -> math
integral x y = embed (Integral x y)
{-# INLINE integral #-}
{-# SPECIALIZE INLINE integral :: Tamagoh.Term Math -> Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE integral :: Hegg.Fix Math -> Hegg.Fix Math -> Hegg.Fix Math #-}

add :: (Corecursive math, Base math ~ Math) => math -> math -> math
add x y = embed (x :+ y)
{-# INLINE add #-}
{-# SPECIALIZE INLINE add :: Tamagoh.Term Math -> Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE add :: Hegg.Fix Math -> Hegg.Fix Math -> Hegg.Fix Math #-}

sub :: (Corecursive math, Base math ~ Math) => math -> math -> math
sub x y = embed (x :- y)
{-# INLINE sub #-}
{-# SPECIALIZE INLINE sub :: Tamagoh.Term Math -> Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE sub :: Hegg.Fix Math -> Hegg.Fix Math -> Hegg.Fix Math #-}

mul :: (Corecursive math, Base math ~ Math) => math -> math -> math
mul x y = embed (x :* y)
{-# INLINE mul #-}
{-# SPECIALIZE INLINE mul :: Tamagoh.Term Math -> Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE mul :: Hegg.Fix Math -> Hegg.Fix Math -> Hegg.Fix Math #-}

quo :: (Corecursive math, Base math ~ Math) => math -> math -> math
quo x y = embed (x :/ y)
{-# INLINE quo #-}
{-# SPECIALIZE INLINE quo :: Tamagoh.Term Math -> Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE quo :: Hegg.Fix Math -> Hegg.Fix Math -> Hegg.Fix Math #-}

pow :: (Corecursive math, Base math ~ Math) => math -> math -> math
pow x y = embed (x :^ y)
{-# INLINE pow #-}
{-# SPECIALIZE INLINE pow :: Tamagoh.Term Math -> Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE pow :: Hegg.Fix Math -> Hegg.Fix Math -> Hegg.Fix Math #-}

lnE :: (Corecursive math, Base math ~ Math) => math -> math
lnE x = embed (Ln x)
{-# INLINE lnE #-}
{-# SPECIALIZE INLINE lnE :: Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE lnE :: Hegg.Fix Math -> Hegg.Fix Math #-}

sqrtE :: (Corecursive math, Base math ~ Math) => math -> math
sqrtE x = embed (Sqrt x)
{-# INLINE sqrtE #-}
{-# SPECIALIZE INLINE sqrtE :: Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE sqrtE :: Hegg.Fix Math -> Hegg.Fix Math #-}

sinE :: (Corecursive math, Base math ~ Math) => math -> math
sinE x = embed (Sin x)
{-# INLINE sinE #-}
{-# SPECIALIZE INLINE sinE :: Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE sinE :: Hegg.Fix Math -> Hegg.Fix Math #-}

cosE :: (Corecursive math, Base math ~ Math) => math -> math
cosE x = embed (Cos x)
{-# INLINE cosE #-}
{-# SPECIALIZE INLINE cosE :: Tamagoh.Term Math -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE cosE :: Hegg.Fix Math -> Hegg.Fix Math #-}

lit :: (Corecursive math, Base math ~ Math) => Double -> math
lit x = embed (Const x)
{-# INLINE lit #-}
{-# SPECIALIZE INLINE lit :: Double -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE lit :: Double -> Hegg.Fix Math #-}

var :: (Corecursive math, Base math ~ Math) => String -> math
var x = embed (Var x)
{-# INLINE var #-}
{-# SPECIALIZE INLINE var :: String -> Tamagoh.Term Math #-}
{-# SPECIALIZE INLINE var :: String -> Hegg.Fix Math #-}

type instance Base (Corecursively a) = Base a

newtype Corecursively a = Corecursively {unwrap :: a}

instance (Corecursive a, Functor (Base a)) => Corecursive (Corecursively a) where
  embed = Corecursively . embed . fmap unwrap
  {-# INLINE embed #-}

instance (Base a ~ Math, Corecursive a) => Num (Corecursively a) where
  (+) = add
  (-) = sub
  (*) = mul
  abs _ = error "abs is not defined for Tamagoh.Term Math"
  signum _ = error "signum is not defined for Tamagoh.Term Math"
  fromInteger = lit . fromInteger

instance (Base a ~ Math, Corecursive a) => Fractional (Corecursively a) where
  (/) = quo
  fromRational = lit . fromRational

instance (Base a ~ Math, Corecursive a) => Floating (Corecursively a) where
  pi = lit pi
  exp x = pow (lit (exp 1)) x
  log = lnE
  sin = sinE
  cos = cosE
  asin = error "asin is not defined for Tamagoh.Term Math"
  acos = error "acos is not defined for Tamagoh.Term Math"
  atan = error "atan is not defined for Tamagoh.Term Math"
  sinh = error "sinh is not defined for Tamagoh.Term Math"
  cosh = error "cosh is not defined for Tamagoh.Term Math"
  asinh = error "asinh is not defined for Tamagoh.Term Math"
  acosh = error "acosh is not defined for Tamagoh.Term Math"
  atanh = error "atanh is not defined for Tamagoh.Term Math"

deriving via
  Corecursively (Tamagoh.Term Math)
  instance
    Num (Tamagoh.Term Math)

deriving via
  Corecursively (Tamagoh.Term Math)
  instance
    Fractional (Tamagoh.Term Math)

deriving via
  Corecursively (Tamagoh.Term Math)
  instance
    Floating (Tamagoh.Term Math)

deriving via
  Corecursively (Tamagoh.Pattern Math v)
  instance
    Num (Tamagoh.Pattern Math v)

deriving via
  Corecursively (Tamagoh.Pattern Math v)
  instance
    Fractional (Tamagoh.Pattern Math v)

deriving via
  Corecursively (Tamagoh.Pattern Math v)
  instance
    Floating (Tamagoh.Pattern Math v)

deriving via
  Corecursively (Hegg.Fix Math)
  instance
    Num (Hegg.Fix Math)

deriving via
  Corecursively (Hegg.Fix Math)
  instance
    Fractional (Hegg.Fix Math)

deriving via
  Corecursively (Hegg.Fix Math)
  instance
    Floating (Hegg.Fix Math)

newtype ConstantFold = ConstantFold {value :: Maybe Double}
  deriving (Show, Eq, Ord, GHC.Generic)
  deriving newtype (Copyable, Consumable, Dupable, Movable, Hashable, Display)

isFolded :: ConstantFold -> Bool
{-# INLINE isFolded #-}
isFolded = coerce $ isJust @Double

liftBin :: (Double -> Double -> Double) -> ConstantFold -> ConstantFold -> ConstantFold
{-# INLINE liftBin #-}
liftBin f = coerce $ liftA2 @Maybe @Double f

liftUnary :: (Double -> Double) -> ConstantFold -> ConstantFold
{-# INLINE liftUnary #-}
liftUnary f = coerce $ fmap @Maybe @Double f

foldConstF :: Math ConstantFold -> ConstantFold
{-# INLINE foldConstF #-}
foldConstF = \case
  Const x -> ConstantFold (Just x)
  l :+ r -> liftBin (+) l r
  l :- r -> liftBin (-) l r
  l :* r -> liftBin (*) l r
  l :/ r ->
    if r /= ConstantFold (Just 0.0)
      then liftBin (/) l r
      else ConstantFold Nothing
  Sin x -> liftUnary P.sin x
  Cos x -> liftUnary P.cos x
  Sqrt x | Just y <- x.value, y >= 0 -> liftUnary P.sqrt x
  Ln x | Just y <- x.value, y > 0 -> liftUnary P.log x
  _ -> ConstantFold Nothing

instance Semilattice ConstantFold where
  ConstantFold Nothing /\ r = r
  l /\ ConstantFold Nothing = l
  ConstantFold (Just x) /\ ConstantFold (Just y)
    | x == y = ConstantFold (Just x)
    | otherwise = ConstantFold (Just x) -- Floating-point number can be approximated
  {-# INLINE (/\) #-}

instance Tamagoh.Analysis Math ConstantFold where
  makeAnalysis = foldConstF . fmap snd
  {-# INLINE makeAnalysis #-}
  modifyAnalysis constFoldL eid egraph = Control.do
    (Ur anal, egraph) <- Raw.getAnalysis eid <$~ egraph
    case value . view constFoldL =<< anal of
      Nothing -> Control.pure (consume egraph)
      Just v -> Control.do
        (Ur _, Ur eid', egraph) <- Raw.addTerm (embed $ Const v) egraph
        if eid P.== eid'
          then Control.do
            Control.pure (consume egraph)
          else Control.do
            Control.void (Raw.unsafeMerge eid eid' egraph)

instance Hegg.Analysis ConstantFold Math where
  makeA = foldConstF
  {-# INLINE makeA #-}
  joinA = (/\)
  {-# INLINE joinA #-}
  modifyA eid egraph = case egraph ^. Hegg._class eid . Hegg._data of
    ConstantFold Nothing -> egraph
    ConstantFold (Just v) ->
      let (eid', egraph') = Hegg.represent (lit v) egraph
       in snd $ Hegg.merge eid eid' egraph'

newtype AstSize = AstSize Word
  deriving (Show, Eq, Ord, GHC.Generic)
  deriving newtype (Num, Copyable, Consumable, Dupable, Movable, Hashable, Display)

astSize :: Hegg.CostFunction Math AstSize
{-# INLINE astSize #-}
astSize = (+ 1) . sum

instance Tamagoh.CostModel AstSize Math where
  costFunction = coerce astSize
  {-# INLINE costFunction #-}

data SideCond
  = IsNotZero String
  | IsSym String
  | IsConst String
  | IsConstOrDistinctVar String String
  deriving (Show, Eq, Ord, GHC.Generic)

data Rule = Rule
  { name :: String
  , lhs :: Tamagoh.Pattern Math String
  , rhs :: Tamagoh.Pattern Math String
  , conditions :: [SideCond]
  }

named :: String -> Rule -> Rule
{-# INLINE named #-}
named n = \r -> r {name = n}

(==>) :: Tamagoh.Pattern Math String -> Tamagoh.Pattern Math String -> Rule
{-# INLINE (==>) #-}
(==>) l r = Rule {name = "", lhs = l, rhs = r, conditions = []}

(@?) :: Rule -> [SideCond] -> Rule
{-# INLINE (@?) #-}
(@?) r conditions = r {conditions}

infix 1 @?

infix 5 ==>

toTamagohRule :: (HasConstantFold d) => Rule -> Tamagoh.Rule Math d String
{-# INLINE toTamagohRule #-}
toTamagohRule rule =
  Tamagoh.Rule
    { Tamagoh.lhs = rule.lhs
    , Tamagoh.rhs = rule.rhs
    , Tamagoh.name = rule.name
    , Tamagoh.condition = toTamagohCondition rule.conditions
    }

toHeggRule :: (HasConstantFold d) => Rule -> Hegg.Rewrite d Math
{-# INLINE toHeggRule #-}
toHeggRule rule =
  foldl' (Hegg.:|) (toHeggPattern rule.lhs Hegg.:= toHeggPattern rule.rhs) $
    toHeggCondition rule.conditions

toHeggPattern :: Tamagoh.Pattern Math String -> Hegg.Pattern Math
{-# INLINE toHeggPattern #-}
toHeggPattern = \case
  Tamagoh.Metavar v -> Hegg.VariablePattern v
  Tamagoh.PNode fpat ->
    Hegg.NonVariablePattern $ fmap toHeggPattern fpat

toTamagohCondition ::
  (HasConstantFold d) =>
  [SideCond] -> Maybe (Tamagoh.SideCondition Math d String)
toTamagohCondition conds = Tamagoh.SideCondition . foldl1' (.&.) . fmap fromCond <$> NE.nonEmpty conds
  where
    fromCond (IsNotZero s) = isNonZero s
    fromCond (IsSym s) = isSymbol s
    fromCond (IsConst s) = isConstant s
    fromCond (IsConstOrDistinctVar s1 s2) = isConstantOrDistinctVar s1 s2

getVar :: String -> Hegg.VarsState -> Hegg.Subst -> Hegg.ClassId
getVar v vss subst = fromJust $ Hegg.lookupSubst (Hegg.findVarName vss v) subst

toHeggCondition :: (HasConstantFold d) => [SideCond] -> [Hegg.RewriteCondition d Math]
toHeggCondition conds = fromCond <$> conds
  where
    fromCond (IsNotZero s) vss subst egr =
      egr ^. Hegg._class (getVar s vss subst) . Hegg._data . constFoldL /= ConstantFold (Just 0.0)
    fromCond (IsSym s) vss subst egr =
      any (Hegg.unNode >>> \case Var {} -> True; _ -> False) $
        egr ^. Hegg._class (getVar s vss subst) . Hegg._nodes
    fromCond (IsConst s) vss subst egr =
      isJust $
        (.value) $
          egr ^. Hegg._class (getVar s vss subst) . Hegg._data . constFoldL
    fromCond (IsConstOrDistinctVar s1 s2) vss subst egr =
      let v' = getVar s1 vss subst
          w' = getVar s2 vss subst
       in (Hegg.eClassId (egr ^. Hegg._class v') /= Hegg.eClassId (egr ^. Hegg._class w'))
            && ( isJust (egr ^. Hegg._class v' . Hegg._data . constFoldL).value
                   || any ((\case Var {} -> True; _ -> False) . Hegg.unNode) (egr ^. Hegg._class v' . Hegg._nodes)
               )

class HasConstantFold a where
  constFoldL :: Lens' a ConstantFold

instance HasConstantFold ConstantFold where
  constFoldL = id

instance HasConstantFold (a, ConstantFold) where
  constFoldL = _2

instance HasConstantFold (ConstantFold, a) where
  constFoldL = _1

mathRulesTamagoh :: (HasConstantFold d) => [Tamagoh.Rule Math d String]
mathRulesTamagoh = toTamagohRule <$> rules

mathRulesHegg :: (HasConstantFold d) => [Hegg.Rewrite d Math]
mathRulesHegg = toHeggRule <$> rules

rules :: [Rule]
rules =
  [ -- Basic laws
    named "comm-add" $ a + b ==> b + a
  , named "comm-mul" $ a * b ==> b * a
  , named "assoc-add" $ a + (b + c) ==> (a + b) + c
  , named "assoc-mul" $ a * (b * c) ==> (a * b) * c
  , -- Canonisation
    named "sub-canon" $ a - b ==> a + (-1 * b)
  , named "div-canon" $ a / b ==> a * (b ** (-1)) @? [IsNotZero "b"]
  , -- Identities & Absoptions
    named "zero-add" $ 0 + a ==> a
  , named "zero-mul" $ 0 * a ==> 0
  , named "one-mul" $ 1 * a ==> a
  , -- Opposite identities
    -- named "add-zero" $ a ==> a + 0
    named "mul-one" $ a ==> a * 1
  , -- Cancel laws
    named "cancel-sub" $ a - a ==> 0
  , named "cancel-div" $ a / a ==> 1 @? [IsNotZero "a"]
  , -- Distributive laws and its opposite
    named "dist-mul-over-add" $ a * (b + c) ==> (a * b) + (a * c)
  , named "fact-mul-over-add" $ (a * b) + (a * c) ==> a * (b + c)
  , -- Power  laws
    named "pow-mul" $ (a ** b) * (a ** c) ==> a ** (b + c)
  , named "pow0" $ a ** 0 ==> 1 @? [IsNotZero "a"]
  , named "pow1" $ a ** 1 ==> a
  , named "pow2" $ a ** 2 ==> a * a
  , named "pow-recip" $ a ** (-1) ==> 1 / a @? [IsNotZero "a"]
  , named "recip-mul-div" $ a * (1 / a) ==> 1 @? [IsNotZero "a"]
  , -- Derivations
    named "d-variable" $ diff x x ==> 1 @? [IsSym "x"]
  , named "d-constant" $ diff x c ==> 0 @? [IsSym "x", IsConstOrDistinctVar "c" "x"]
  , named "d-add" $ diff x (a + b) ==> diff x a + diff x b
  , named "d-mul" $ diff x (a * b) ==> a * diff x b + b * diff x a
  , named "d-sin" $ diff x (sin x) ==> cos x
  , named "d-cos" $ diff x (cos x) ==> -1 * sin x
  , named "d-ln" $ diff x (lnE x) ==> 1 / x @? [IsNotZero "x"]
  , named "d-power" $
      diff x (f ** g) ==> (f ** g) * ((diff x f * (g / f)) + (diff x g * lnE f))
        @? [IsNotZero "f", IsNotZero "g"]
  , named "i-one" $ integral 1 x ==> x
  , named "i-power-const" $
      integral (x ** c) x ==> (x ** (c + 1)) / (c + 1) @? [IsConst "c"]
  , named "i-cos" $ integral (cos x) x ==> sin x
  , named "i-sin" $ integral (sin x) x ==> -1 * cos x
  , named "i-sum" $ integral (f + g) x ==> integral f x + integral g x
  , named "i-dif" $ integral (f - g) x ==> integral f x - integral g x
  , named "i-parts" $ integral (f * g) x ==> f * integral g x - integral (diff x f * integral g x) x
  ]
  where
    a = Tamagoh.Metavar "a"
    b = Tamagoh.Metavar "b"
    c = Tamagoh.Metavar "c"
    f = Tamagoh.Metavar "f"
    g = Tamagoh.Metavar "g"
    x = Tamagoh.Metavar "x"

isNonZero :: (HasConstantFold d) => String -> HM.HashMap String (MatchInfo Math d) -> Bool
{-# INLINE isNonZero #-}
{-# SPECIALIZE INLINE isNonZero :: String -> HM.HashMap String (MatchInfo Math ConstantFold) -> Bool #-}
isNonZero v = \vars -> view constFoldL (vars HM.! v).analysis /= ConstantFold (Just 0.0)

isSymbol :: String -> HM.HashMap String (MatchInfo Math d) -> Bool
{-# INLINE isSymbol #-}
isSymbol v = \vars -> isVarNode $ (vars HM.! v).nodes

isConstant :: (HasConstantFold d) => String -> HM.HashMap String (MatchInfo Math d) -> Bool
{-# INLINE isConstant #-}
isConstant v = \vars -> case (vars HM.! v).analysis ^. constFoldL of
  ConstantFold (Just _) -> True
  ConstantFold Nothing -> False

isConstantOrDistinctVar ::
  (HasConstantFold d) =>
  String ->
  String ->
  HM.HashMap String (MatchInfo Math d) ->
  Bool
{-# INLINE isConstantOrDistinctVar #-}
isConstantOrDistinctVar v1 v2 = \vars ->
  let v = vars HM.! v1
      w = vars HM.! v2
   in v.eclassId /= w.eclassId && (isFolded (v.analysis ^. constFoldL) || isVarNode v.nodes)

isVarNode :: [Tamagoh.ENode Math] -> Bool
isVarNode = any $ (.unwrap) >>> \case Var {} -> True; _ -> False

type Predicate d = HM.HashMap String (MatchInfo Math d) -> Bool

(.&.) :: Predicate d -> Predicate d -> Predicate d
{-# INLINE (.&.) #-}
p1 .&. p2 = \vars -> p1 vars && p2 vars

infixr 3 .&.

newtype BenchCost = BenchCost Word
  deriving (Show, Eq, Ord, GHC.Generic)
  deriving newtype (Num, Copyable, Consumable, Dupable, Movable, Hashable, Display)

symCost :: Math BenchCost -> BenchCost
{-# INLINE symCost #-}
symCost = \case
  a :^ b -> a + b + 6
  a :/ b -> a + b + 5
  a :- b -> a + b + 4
  a :* b -> a + b + 4
  a :+ b -> a + b + 2
  Diff x f -> x + f + 500
  Integral f x -> f + x + 20000
  Sin x -> x + 20
  Cos x -> x + 20
  Sqrt x -> x + 30
  Ln x -> x + 30
  Var {} -> 1
  Const {} -> 1

instance Tamagoh.CostModel BenchCost Math where
  costFunction = (+ 1) . sum
