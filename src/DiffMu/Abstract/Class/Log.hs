

module DiffMu.Abstract.Class.Log where

import DiffMu.Prelude

class Monad m => MonadLog m where
  log  :: String -> m ()
  debug  :: String -> m ()
  info  :: String -> m ()
  warn :: String -> m ()
  logForce  :: String -> m ()
  withLogLocation :: String -> m a -> m a



