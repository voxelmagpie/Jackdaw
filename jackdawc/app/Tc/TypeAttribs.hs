-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Tc.TypeAttribs where

import Control.Monad (forM)
import Hir qualified as H
import Names (Attribute (Attribute))
import Prelude2
import Tc.State (MonadHirRead' (getTDef))

typeIsUnsafe :: (MonadHirRead' m) => H.Type -> m Bool
typeIsUnsafe = \case
  H.BoolType -> pure False
  H.NumPrimType _ -> pure False
  H.ANamedType id -> do
    tsDef <- getTDef id
    pure $ Attribute "Unsafe" `elem` (H.tDefCommon tsDef).attributes
  H.TupleType xs -> or <$> forM (toList xs) typeIsUnsafe
  H.AFnType _ -> pure False
  H.AnAccessorType _ -> pure False
  H.AnIteratorType _ -> undefined
  H.AnAccessorIteratorType _ -> undefined
  H.PtrType _ -> pure True
  H.ConstPtrType _ -> pure False
  H.ArrayType elType _ -> typeIsUnsafe elType
  H.SliceType _ -> pure False
