
module DiffMu.Core.FormalTerm where

import DiffMu.Prelude
-- import DiffMu.Core.Definitions


data SingleSub x a = (:=) x a
  deriving (Show)
type Sub x a = [SingleSub x a]

-- class HasSub t x a where

-- class HasImpossibleError e where
--   impossible :: Text -> e

class Monad t => MonadImpossible t where
  impossible :: String -> t a

-- class (MonadError e t, HasImpossibleError e) => MonadImpossible t where

-- terms of type a, with variables of type x
class (MonadImpossible t, Eq x, Show x, Show a) => TermSubstitute t x a | a -> x where
  substitute :: a -> SingleSub x a -> t a

-- data AnySub t where
--   AnySub :: TermSubstitute t x a => Sub x a -> AnySub t

instance (TermSubstitute t x a) => SemigroupM t (Sub x a) where
  (⋆) as bs = foldM f as bs
    where f :: Sub x a -> SingleSub x a -> t (Sub x a)
          f as b = (<>) <$> mapM (\a -> apply a b) as <*> pure [b]

          apply :: SingleSub x a -> SingleSub x a -> t (SingleSub x a)
          apply (x := a) (y := b) | x == y    = impossible $ "Tried to extend a set of substitutions which already contains " <> show (x := a) <> " with a new substitution of the same variable, " <> show (y := b) <> "."
          apply (x := a) (y := b) | otherwise = (:=) x <$> (substitute a (y := b))

instance (TermSubstitute t x a) => MonoidM t (Sub x a) where
  neutral = pure []



-- instance ModuleM t (AnySub t) a where


-- class (MonadTC x a t) => MonadTC_Eq x a t where
--   -- add

-- class Constraint2 t c where
--   evaluate_ :: c -> t (Maybe c)

-- data Evaluated = IsEvaluated | NotEvaluated

-- data Constr c = Constr Evaluated c


-- evaluate :: Constraint2 t c => Constr c -> t (Constr c)
-- evaluate (Constr IsEvaluated c) = undefined -- pure $ Constr IsEvaluated c
-- evaluate (Constr NotEvaluated c) = undefined


