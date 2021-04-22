
module DiffMu.Abstract.Data.NameCtx where

import DiffMu.Prelude
import DiffMu.Abstract.Class.Term

-- import DiffMu.Abstract.Class.Term
-- import DiffMu.Abstract.MonadTC
-- import DiffMu.Abstract.MonadicPolynomial

import qualified Data.Text as T

---------------------------------------------------------------------
-- A simple (non-kinded) context for names
data NameCtx = NameCtx
  { names :: [Symbol]
  , currentCtr :: Int
  }
  deriving (Generic)
instance Default NameCtx
instance Show NameCtx where
  show (NameCtx names _) = "[" <> intercalate ", " (show <$> names) <> "]"

newName :: Text -> NameCtx -> (Symbol, NameCtx)
newName (hint) (NameCtx names ctr) =
  let name = Symbol (hint <> "_" <> T.pack (show ctr))
  in (name , NameCtx (name : names) (ctr +! 1))




---------------------------------------------------------------------
-- A kinded context for names

data SingSomeK (v :: j -> *) where
  SingSomeK :: (Show (Demote (KindOf k)), SingKind (KindOf k), SingI k, Typeable k) => v k -> SingSomeK v

instance KShow v => Show (SingSomeK v) where
  show (SingSomeK (s :: v k)) = show s <> " : " <> show (demote @k)

data KindedNameCtx (v :: j -> *) = KindedNameCtx
  {
    namesK :: [SingSomeK v]
  , currentCtrK :: Int
  }
instance Default (KindedNameCtx v) where
  def = KindedNameCtx [] 0

instance KShow v => Show (KindedNameCtx v) where
  show (KindedNameCtx names _) = "[" <> intercalate ", " (show <$> names) <> "]"

newKindedName :: (Show (Demote (KindOf k)), SingKind (KindOf k), SingI k, FromSymbol v, Typeable k) => Text -> KindedNameCtx v -> (v k, KindedNameCtx v)
newKindedName (hint) (KindedNameCtx names ctr) =
  let name = (fromSymbol (Symbol (hint <> "_" <> T.pack (show ctr))))
  in (name , KindedNameCtx (SingSomeK (name) : names) (ctr +! 1))


removeNameBySubstitution :: ((forall j. Eq (v j)), Typeable k) => Sub v a k -> KindedNameCtx v -> KindedNameCtx v
removeNameBySubstitution ((x :: v k) := _) (KindedNameCtx names ctr) =
  let f :: Typeable j => v j -> Maybe (v j)
      f (v :: v j) = case testEquality (typeRep @j) (typeRep @k) of
        Just Refl -> case v == x of
          True -> Nothing
          False -> Just v
        Nothing -> Just v
      g :: SingSomeK v -> Maybe (SingSomeK v)
      g (SingSomeK x) = SingSomeK <$> (f x)
      names' = [n | (Just n) <- g <$> names]
  in KindedNameCtx names' ctr


