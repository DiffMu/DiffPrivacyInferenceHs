
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

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :-----: b) where
  showPretty (a :-----: b) = showPretty a
                   <> "\n"
                   <> "---------------------------------------------------------"
                   <> "\n"
                   <> showPretty b

instance (Normalize t a, Normalize t b) => Normalize t (a :-----: b) where

--------------

infixl 5 :\\:
data (:\\:) a b = (:\\:) a b

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :\\: b) where
  showPretty (a :\\: b) = showPretty a
                   <> "\n"
                   <> showPretty b

instance (Normalize t a, Normalize t b) => Normalize t (a :\\: b) where



-------------------------------------------------------------------------
-- Horizontal combination

infixl 6 :<>:
data (:<>:) a b = (:<>:) a b

instance (ShowPretty a, ShowPretty b) => ShowPretty (a :<>: b) where
  showPretty (a :<>: b) = showPretty a <> " " <> showPretty b

instance (Normalize t a, Normalize t b) => Normalize t (a :<>: b) where


-- -------

-- data (:<.:) a = (:<.:) a String

-- instance (ShowPretty a) => ShowPretty (:<.:) a where
--   showPretty (a :<.: b) = showPretty a <> " " <> showPretty b

-- instance (Normalize t a) => Normalize t ((:<.:) a) where
