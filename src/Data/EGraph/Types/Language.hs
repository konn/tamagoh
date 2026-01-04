{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.EGraph.Types.Language (
  Language,
  deriveLanguage,
) where

import Control.Monad (filterM)
import Data.Deriving (deriveEq1, deriveOrd1)
import Data.EGraph.EMatch.Relational.Database
import Data.EGraph.Types.Term
import Data.Functor.Classes
import Data.Hashable
import Data.Hashable.Lifted (Hashable1)
import Data.List (unsnoc)
import Data.Traversable qualified as P
import Data.Unrestricted.Linear.Lifted (Copyable1, Movable1)
import GHC.Generics qualified as GHC
import Generics.Linear qualified as LG
import Generics.Linear.TH qualified as GL
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Text.Show.Deriving (deriveShow1)

type Language l =
  ( Hashable1 l
  , Movable1 l
  , P.Traversable l
  , Matchable l
  , Copyable1 l
  , HasDatabase l
  )

data DeriveTarget
  = DvEq
  | DvOrd
  | DvShow
  | DvFunctor
  | DvFoldable
  | DvTraversable
  | DvGeneric
  | DvGeneric1
  | DvLinearGeneric
  | DvLinearGeneric1
  | DvEq1
  | DvOrd1
  | DvShow1
  | DvHashable
  | DvHashable1
  | DvMovable1
  | DvCopyable1
  | DvMatchable
  deriving (Show, Eq, Ord, Enum, Bounded)

derivations :: [DeriveTarget]
derivations =
  [minBound .. maxBound]

classHead :: LanguageDef -> DeriveTarget -> (Name, [Type])
classHead langDef = \case
  DvEq -> (''Eq, [langDef.fullType])
  DvOrd -> (''Ord, [langDef.fullType])
  DvShow -> (''Show, [langDef.fullType])
  DvFunctor -> (''Functor, [langDef.rank1Type])
  DvFoldable -> (''Foldable, [langDef.rank1Type])
  DvTraversable -> (''Traversable, [langDef.rank1Type])
  DvGeneric -> (''GHC.Generic, [langDef.fullType])
  DvGeneric1 -> (''GHC.Generic1, [langDef.rank1Type])
  DvLinearGeneric -> (''LG.Generic, [langDef.fullType])
  DvLinearGeneric1 -> (''LG.Generic1, [langDef.rank1Type])
  DvEq1 -> (''Eq1, [langDef.rank1Type])
  DvOrd1 -> (''Ord1, [langDef.rank1Type])
  DvShow1 -> (''Show1, [langDef.rank1Type])
  DvHashable -> (''Hashable, [langDef.fullType])
  DvHashable1 -> (''Hashable1, [langDef.rank1Type])
  DvMovable1 -> (''Movable1, [langDef.rank1Type])
  DvCopyable1 -> (''Copyable1, [langDef.rank1Type])
  DvMatchable -> (''Matchable, [langDef.rank1Type])

{- |
Derives all _missing_ instances required for 'Language' constraint synonym, ignoring the existing ones.
You may need to bring 'GHC.Generically1' into the scope and the following extensions must be enabled:

  * @TemplateHaskell@ (of course)
  * @DataKinds@
  * @DeriveAnyClass@
  * @DeriveGeneric@
  * @DeriveTraversable@
  * @DerivingStrategies@
  * @DerivingVia@
  * @LinearTypes@
  * @TypeFamilies@
  * @UndecidableInstances@
  * @PartialTypeSignatures@ (with possibly @-Wno-partial-type-signatures@ option)
-}
deriveLanguage :: Name -> DecsQ
deriveLanguage name = do
  info <- reifyDatatype name
  langDef <- checkKind info
  todos <- filterM (fmap null . uncurry reifyInstances . classHead langDef) derivations
  concat <$> mapM (derive langDef) todos

derive :: LanguageDef -> DeriveTarget -> Q [Dec]
derive lang DvEq = [d|deriving stock instance (_) => Eq $(pure $ lang.fullType)|]
derive lang DvOrd = [d|deriving stock instance (_) => Ord $(pure $ lang.fullType)|]
derive lang DvShow = [d|deriving stock instance (_) => Show $(pure $ lang.fullType)|]
derive lang DvFunctor = [d|deriving stock instance (_) => Functor $(pure $ lang.rank1Type)|]
derive lang DvFoldable = [d|deriving stock instance (_) => Foldable $(pure $ lang.rank1Type)|]
derive lang DvTraversable = [d|deriving stock instance (_) => Traversable $(pure $ lang.rank1Type)|]
derive lang DvGeneric = [d|deriving stock instance GHC.Generic $(pure $ lang.fullType)|]
derive lang DvGeneric1 = [d|deriving stock instance GHC.Generic1 $(pure $ lang.rank1Type)|]
derive lang DvLinearGeneric = GL.deriveGeneric lang.typeName
derive lang DvLinearGeneric1 = GL.deriveGeneric1 lang.typeName
derive lang DvEq1 = deriveEq1 lang.typeName
derive lang DvOrd1 = deriveOrd1 lang.typeName
derive lang DvShow1 = deriveShow1 lang.typeName
derive lang DvHashable = [d|deriving anyclass instance (_) => Hashable $(pure lang.fullType)|]
derive lang DvHashable1 = [d|deriving anyclass instance (_) => Hashable1 $(pure lang.rank1Type)|]
derive lang DvMovable1 = [d|deriving via GHC.Generically1 $(pure lang.rank1Type) instance (_) => Movable1 $(pure lang.rank1Type)|]
derive lang DvCopyable1 = [d|deriving via GHC.Generically1 $(pure lang.rank1Type) instance (_) => Copyable1 $(pure lang.rank1Type)|]
derive lang DvMatchable = [d|deriving via GHC.Generically1 $(pure lang.rank1Type) instance (_) => Matchable $(pure lang.rank1Type)|]

data LanguageDef = LanguageDef
  { typeName :: Name
  , rank1Type :: Type
  , fullType :: Type
  , dtype :: DatatypeInfo
  }

checkKind :: DatatypeInfo -> Q LanguageDef
checkKind dtype = do
  case unsnoc dtype.datatypeInstTypes of
    Just (args, SigT _ StarT) -> do
      names <- mapM (const $ newName "x") args
      name <- newName "v"
      let rank1Type = foldl' AppT (ConT dtype.datatypeName) (map VarT names)
          fullType = AppT rank1Type (VarT name)
          typeName = dtype.datatypeName
      pure $ LanguageDef {..}
    _ -> fail $ "Expected a type constructor of kind (k1 -> .. -> kn -> Type -> Type), but got " <> pprint (foldr (AppT . AppT ArrowT) dtype.datatypeReturnKind dtype.datatypeInstTypes)
