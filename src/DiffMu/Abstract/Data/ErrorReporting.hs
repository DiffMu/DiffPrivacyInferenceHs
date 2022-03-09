
module DiffMu.Abstract.Data.ErrorReporting where

import DiffMu.Prelude
-- import DiffMu.Abstract
-- import DiffMu.Core.Definitions
-- import DiffMu.Core.TC
-- import DiffMu.Core.Logging


instance Monad t => Normalize t Char where


-------------------------------------------------------------------------
-- Vertical combination

infixl 5 :-----:
data (:-----:) a b = (:-----:) a b

instance (Show a, Show b) => Show (a :-----: b) where
  show (a :-----: b) = show a
                   <> "\n"
                   <> "---------------------------------------------------------"
                   <> "\n"
                   <> show b

instance (Normalize t a, Normalize t b) => Normalize t (a :-----: b) where

--------------

infixl 5 :\\:
data (:\\:) a b = (:\\:) a b

instance (Show a, Show b) => Show (a :\\: b) where
  show (a :\\: b) = show a
                   <> "\n"
                   <> show b

instance (Normalize t a, Normalize t b) => Normalize t (a :\\: b) where



-------------------------------------------------------------------------
-- Horizontal combination

infixl 6 :<>:
data (:<>:) a b = (:<>:) a b

instance (Show a, Show b) => Show (a :<>: b) where
  show (a :<>: b) = show a <> " " <> show b

instance (Normalize t a, Normalize t b) => Normalize t (a :<>: b) where


-- -------

-- data (:<.:) a = (:<.:) a String

-- instance (Show a) => Show (:<.:) a where
--   show (a :<.: b) = show a <> " " <> show b

-- instance (Normalize t a) => Normalize t ((:<.:) a) where
