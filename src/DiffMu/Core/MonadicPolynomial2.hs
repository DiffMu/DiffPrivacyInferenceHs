
module DiffMu.Core.MonadicPolynomial2 where

import DiffMu.Prelude
import DiffMu.Core.Term

import qualified Prelude as P
import Data.HashMap.Strict as H

-- foldM

newtype MonCom m v = MonCom (HashMap v m)
  deriving (Generic, Show, Hashable, Eq)
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

-- actions on moncom

newtype ActM a = ActM a
instance (HasMonCom t m v) => ModuleM t (ActM m) (MonCom m v) where
  (↷) (ActM m) (MonCom xs) =
    let g m₁ (v₂,m₂) = do m' <- m₁ ⋆ m₂
                          return (v₂, m')
        f m₁ xs = mapM (g m₁) xs

    in (MonCom <$> H.fromList <$> (f m (H.toList xs))) -- >>= normalize
    -- in (MonCom <$> (f m xs)) -- >>= normalize

newtype ActV a = ActV a
instance (HasMonCom t m v, MonoidM t v) => ModuleM t (ActV v) (MonCom m v) where
  (↷) (ActV v) (MonCom xs) =
    let g v₁ (v₂,m₂) = do v' <- v₁ ⋆ v₂
                          return (v', m₂)
        f v₁ xs = mapM (g v₁) xs

    -- in (MonCom <$> (f v xs)) -- >>= normalize
    in (MonCom <$> H.fromList <$> (f v (H.toList xs))) -- >>= normalize

-- usage as dictionary

class DictKey k => DictLike k v d | d -> k v where
  setValue :: k -> v -> d -> d

class ShowDict k v d | d -> k v where
  showWith :: String -> (k -> v -> String) -> d -> String

instance (DictKey k) => DictLike k v (MonCom v k) where
  setValue v m (MonCom h) = MonCom (H.insert v m h)

instance ShowDict k v (MonCom v k) where
  showWith comma merge (MonCom d) =
    let d' = H.toList d
    in intercalate comma ((\(k,v) -> merge k v) <$> d')





-----------------------------------------------------------
-- LinCom


newtype LinCom r v = LinCom { getLinCom :: (MonCom r v) }
  deriving (Generic, Hashable, Default, Eq, DictLike v r, ShowDict v r)

-- instance Show (LinCom r v) where

injectCoeff :: (HasMonCom t r v, MonoidM t v) => r -> t (LinCom r v)
injectCoeff r = do
  o <- neutral
  return (LinCom (MonCom (H.singleton o r)))

                  -- [(r , o)]))
  -- LinCom <$> ((ActM r) ↷> neutral) -- LinCom (MonCom [(r , o)])

injectCoeffId :: (HasMonCom Identity r v, MonoidM Identity v) => r -> (LinCom r v)
injectCoeffId r = LinCom (MonCom (H.singleton neutralId r))
                          -- [(r, neutralId)])
  -- o <- neutral
  -- return (LinCom (MonCom [(r , o)]))

instance (HasMonCom t r v) => SemigroupM t (LinCom r v) where
  (⋆) (LinCom p) (LinCom q) = LinCom <$> (p ⋆ q)

instance (HasMonCom t r v) => MonoidM t (LinCom r v) where
  neutral = LinCom <$> neutral

instance (HasMonCom t r v, SemiringM t r) => ModuleM t (ActM r) (LinCom r v) where
  -- (↷) r (LinCom p) = LinCom <$> (ActM r ↷ p)

  (↷) (ActM m) (LinCom (MonCom xs)) =
    let g m₁ (v₂,m₂) = do m' <- m₁ ⋅ m₂
                          return (v₂, m')
        f m₁ xs = mapM (g m₁) xs

    in (LinCom <$> MonCom <$> H.fromList <$> (f m (H.toList xs))) -- >>= normalize

instance (HasMonCom t r v, MonoidM t v) => ModuleM t (ActV v) (LinCom r v) where
  (↷) v (LinCom p) = LinCom <$> (v ↷ p)


instance (CMonoidM t r, HasMonCom t r v) => CMonoidM t (LinCom r v)


-- instance (HasOne r, HasMonCom t r v, Pointed v) => HasOne (LinCom r v) where
--   one = LinCom (MonCom [(one, pt)])

instance (SemiringM t r, HasMonCom t r v, MonoidM t v) => SemiringM t (LinCom r v) where
  one = f <$> one <*> neutral
    where f a b = LinCom (MonCom (H.singleton b a))

  (⋅) (LinCom (MonCom p)) q = (f p q)
    -- where f :: [(r,v)] -> LinCom r v -> t (LinCom r v)
    where f :: HashMap v r -> LinCom r v -> t (LinCom r v)
          f map q = H.foldrWithKey' g (LinCom <$> neutral) map
            where g xv xr res = (ActM xr) ↷> ((ActV xv) ↷ q) <+> res
          -- f [] q = 
          -- f ((xr,xv) : xs) q = xr ↷> (xv ↷ q) <+> (f xs q)

type CPolyM r e v = LinCom r (MonCom e v)


injectVarId :: (HasMonCom Identity e v, Hashable e, SemiringM Identity e, SemiringM Identity r) => v -> (CPolyM r e v)
injectVarId v = LinCom (MonCom (H.singleton (MonCom (H.singleton v oneId)) oneId))
                           -- H.singleton (MonCom (H.singleton (v,neutralId)), oneId)))
  -- LinCom (MonCom (H.singleton neutralId r))

-------------------------------------------
-- Term instances


instance (Hashable v, Show v, Show m, Eq v, Eq m, MonoidM Identity m, CheckNeutral Identity m) => Substitute v (MonCom m v) (MonCom m v) where
  substitute σ (MonCom t) =
    let f (v,m) = do vs <- σ v
                     return (ActM m ↷! vs)
    in do x <- mapM f (H.toList t)
          return $ P.foldl (⋆!) neutralId x

instance (Hashable v, Show v, Show m, Eq v, Eq m, MonoidM Identity m, CheckNeutral Identity m) => Term v (MonCom m v) where
  -- type Var (MonCom m v) = v
  var v = MonCom (H.singleton v neutralId) -- [(neutralId, v)]

instance (Eq v, Eq r, Hashable v, CheckNeutral Identity r, SemiringM Identity r) => Substitute v (CPolyM r Int v) (CPolyM r Int v) where
  substitute σ ls =
    let
        f (v, e :: Int) = do vs <- σ v
                             let vslist = take e (repeat vs)
                             return (P.foldl (⋅!) oneId vslist)
        -- f (e , v) = undefined
        g (MonCom mvs, r :: r) = do mvs' <- mapM f (H.toList mvs)
                                    return $ (ActM r) ↷! P.foldl (⋅!) oneId mvs'
        -- g' (r, mvs) = r ↷! g mvs
        h (LinCom (MonCom ls)) = do ls' <- mapM g (H.toList ls)
                                    return $ P.foldl (+!) zeroId ls'
    in h ls

    -- let f (m,v) = do vs <- σ v
    --                  return (m ↷! vs)
    -- in undefined

instance (Show r , Show v) => Show (CPolyM r Int v) where
  show poly = showWith " + " (\vars r -> show r <> "*" <> showWith "*" f vars) poly
    where f v 1 = show v
          f v e = show v <> "^" <> show e


instance (Hashable v, Show v, Show r, Eq v, Eq r, CheckNeutral Identity r, SemiringM Identity r) => Term v (CPolyM r Int v) where
  var v = injectVarId v

    -- LinCom (MonCom [(oneId, var v)])

--------------------------------
-- Normalize instance

instance Normalize t x => Normalize t (MonCom x v) where
  normalize (MonCom map) = MonCom <$> mapM normalize map


-- instance (Normalize t x, Normalize t v, Eq v, Hashable v) => Normalize t (MonCom x v) where
--   normalize (MonCom map) = MonCom <$> H.fromList <$> mapM f (H.toList map)
--     where f (k,v) = (,) <$> normalize k <*> normalize v
