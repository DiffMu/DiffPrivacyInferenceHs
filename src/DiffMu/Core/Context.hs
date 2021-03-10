
module DiffMu.Core.Context where

import DiffMu.Prelude
import DiffMu.Core.Definitions

instance Default (NameCtx) where

instance Default (Ctx a) where

instance Default (Full a) where



instance Semigroup (Ctx a) where
  (<>) a b = undefined

-- instance Semigroup (Full a) where








