
module DiffMu.Abstract.Data.ErrorReporting where

import DiffMu.Prelude
-- import DiffMu.Abstract
-- import DiffMu.Core.Definitions
-- import DiffMu.Core.TC
-- import DiffMu.Core.Logging


instance Monad t => Normalize t Char where
  normalize e = pure


-------------------------------------------------------------------------
-- Vertical combination

infixl 5 :-----:
data (:-----:) a b = (:-----:) a b
  deriving (Show)

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :-----: b) where
  showPretty (a :-----: b) = showPretty a
                   <> "\n"
                   <> "---------------------------------------------------------"
                   <> "\n"
                   <> showPretty b

instance (Normalize t a, Normalize t b) => Normalize t (a :-----: b) where
  normalize e (a :-----: b) = (:-----:) <$> normalize e a <*> normalize e b

--------------

infixl 5 :\\:
data (:\\:) a b = (:\\:) a b
  deriving (Show)

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :\\: b) where
  showPretty (a :\\: b) = showPretty a
                   <> "\n"
                   <> showPretty b

instance (Normalize t a, Normalize t b) => Normalize t (a :\\: b) where
  normalize e (a :\\: b) = (:\\:) <$> normalize e a <*> normalize e b



-------------------------------------------------------------------------
-- Horizontal combination

infixl 6 :<>:
data (:<>:) a b = (:<>:) a b
  deriving (Show)

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :<>: b) where
  showPretty (a :<>: b) = showPretty a <> " " <> showPretty b

instance (Normalize t a, Normalize t b) => Normalize t (a :<>: b) where
  normalize e (a :<>: b) = (:<>:) <$> normalize e a <*> normalize e b


-- -------

-- data (:<.:) a = (:<.:) a String

-- instance (ShowPretty a) => ShowPretty (:<.:) a where
--   showPretty (a :<.: b) = showPretty a <> " " <> showPretty b

-- instance (Normalize t a) => Normalize t ((:<.:) a) where
