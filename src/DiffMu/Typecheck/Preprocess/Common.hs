
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.Common where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Abstract.Data.Permutation
import DiffMu.Typecheck.Operations
import DiffMu.Core.DelayedScope
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.IsFunctionArgument
import DiffMu.Typecheck.Constraint.IsJuliaEqual
import DiffMu.Typecheck.Constraint.CheapConstraints

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace


newtype LightTC l s a = LightTC {runLightTC :: ((StateT s (ExceptT DMException (Writer DMLogMessages))) a)}
  deriving (Functor, Applicative, Monad, MonadState s, MonadError DMException, MonadWriter DMLogMessages)

instance ISing_DMLogLocation l => MonadInternalError (LightTC l s) where
  internalError = throwError . InternalError

instance ISing_DMLogLocation l => MonadImpossible (LightTC l s) where
  impossible = throwError . ImpossibleError

instance ISing_DMLogLocation l => MonadLog (LightTC l a) where
  log = logWithSeverityOfMut Debug
  debug = logWithSeverityOfMut Debug
  info = logWithSeverityOfMut Info
  logForce = logWithSeverityOfMut Force
  warn = logWithSeverityOfMut Warning
  withLogLocation loc action = internalError "setting of location for logging in mtc not implemented"


-- logging
logWithSeverityOfMut :: forall l a. ISing_DMLogLocation l => DMLogSeverity -> String -> LightTC l a ()
logWithSeverityOfMut sev text = do
  -- here we split the messages at line breaks (using `lines`)
  -- in order to get consistent looking output (every line has a header)
  let messages = DMLogMessage sev (singDMLogLocation (Proxy @l)) <$> (reverse $ lines text)
  tell (DMLogMessages messages)

-- lifting

liftNewLightTC :: Default s => LightTC l s a -> TC a
liftNewLightTC a =
  let s = runStateT (runLightTC a) def
  in TCT (StateT (\t -> fmap (\(a,_) -> (a,def)) s))

liftLightTC :: s -> (s -> t) -> LightTC k s a -> LightTC l t a
liftLightTC start f a =
  let s = runStateT (runLightTC a) start
  in LightTC (StateT (\t -> fmap (\(a,x) -> (a,f x)) s))


