
module DiffMu.Core.MonadicPolynomial2 where

import DiffMu.Prelude
import DiffMu.Core.Term

-- import qualified Prelude as P
import Data.HashMap.Strict as H


newtype MonCom m v = MonCom (HashMap v m)
  deriving (Generic, Show, Hashable)
instance Default (MonCom m v) where
  def = MonCom H.empty

class (MonoidM t m, CheckNeutral t m, Eq v, Hashable v)    => HasMonCom t m v
instance (MonoidM t m, CheckNeutral t m, Eq v, Hashable v) => HasMonCom t m v


instance (HasMonCom t m v) => SemigroupM t (MonCom m v) where
  (⋆) (MonCom m) (MonCom n) = MonCom <$> H.foldlWithKey f (pure m) n
    where f mm x a = do
            mm' <- mm
            case H.lookup x mm' of
              Just a' -> do a'' <- a ⋆ a'
                            return (H.insert x a'' mm')
              Nothing -> return (H.insert x a mm')

instance (HasMonCom t m v) => MonoidM t (MonCom m v) where
  neutral = pure (MonCom H.empty)

class DictKey k => DictLike k v d where
  setValue :: k -> v -> d -> d

instance DictKey k => DictLike k v (MonCom v k) where
  setValue v m (MonCom h) = MonCom (H.insert v m h)


