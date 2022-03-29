
module DiffMu.Abstract.Data.HashMap where

import DiffMu.Prelude

import Data.HashMap.Strict as H

instance Normalize t v => Normalize t (HashMap k v) where
  normalize nt map = mapM (normalize nt) map


class DictKey k => DictLikeM t k v d | d -> k v where
  setValueM :: k -> v -> d -> t d
  getValueM :: k -> d -> t (Maybe v)
  deleteValueM :: k -> d -> t d

class DictKey k => DictLike k v d | d -> k v where
  setValue :: k -> v -> d -> d
  getValue :: k -> d -> Maybe v
  deleteValue :: k -> d -> d
  emptyDict :: d
  isEmptyDict :: d -> Bool
  getAllKeys :: d -> [k]
  getAllElems :: d -> [v]
  getAllKeyElemPairs :: d -> [(k,v)]
  fromKeyElemPairs :: [(k,v)] -> d

