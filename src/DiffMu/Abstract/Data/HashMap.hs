
module DiffMu.Abstract.Data.HashMap where

import DiffMu.Prelude

import Data.HashMap.Strict as H

instance Normalize t v => Normalize t (HashMap k v) where
  normalize map = mapM normalize map




