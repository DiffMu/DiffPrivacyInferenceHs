
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.Common where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.TC
import DiffMu.Core.Logging

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace


newtype LightTC l s a = LightTC {runLightTC :: ((StateT s (ExceptT LocatedDMException (Writer (DMMessages (LightTC l s) )))) a)}
  deriving (Functor, Applicative, Monad, MonadState s, MonadError LocatedDMException, MonadWriter (DMMessages (LightTC l s)))

instance ISing_DMLogLocation l => MonadInternalError (LightTC l s) where
  internalError = throwUnlocatedError . InternalError

instance ISing_DMLogLocation l => MonadImpossible (LightTC l s) where
  impossible = throwUnlocatedError . ImpossibleError

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
  tell (DMMessages messages [])

-- lifting

newtype WrapMessageLight a = WrapMessageLight a
instance Show a => Show (WrapMessageLight a) where
  show (WrapMessageLight a) = show a
instance Monad m => Normalize m (WrapMessageLight a) where
  normalize e x = pure x

liftNewLightTC :: Default s => LightTC l s a -> TC a
liftNewLightTC a =
  let s = runExceptT $ runStateT (runLightTC a) def

      g :: DMMessages (LightTC l1 s1) -> DMMessages (TCT Identity)
      g (DMMessages xs ys) = DMMessages xs (fmap (\(DMPersistentMessage a) -> DMPersistentMessage (WrapMessageLight a)) ys)

      f :: (Either LocatedDMException (a, s), DMMessages (LightTC l s)) -> (Either LocatedDMException (a, Full), DMMessages (TCT Identity))
      f (Left a, b) = (Left a , g b)
      f (Right (a, s), b) = (Right (a, def), g b)

  in TCT (StateT (\t -> ExceptT (WriterT (return (f $ runWriter $ s)))))

liftLightTC :: forall s t k l a. s -> (s -> t) -> LightTC k s a -> LightTC l t a
liftLightTC start conv a =
  let s = runExceptT $ runStateT (runLightTC a) start

      g :: DMMessages (LightTC k1 s) -> DMMessages (LightTC k2 t)
      g (DMMessages xs ys) = DMMessages xs (fmap (\(DMPersistentMessage a) -> DMPersistentMessage (WrapMessageLight a)) ys)

      f :: (Either LocatedDMException (a, s), DMMessages (LightTC k1 s)) -> (Either LocatedDMException (a, t), DMMessages (LightTC l t))
      f (Left a, b) = (Left a , g b)
      f (Right (a, s), b) = (Right (a, conv s), g b)

  in LightTC (StateT (\t -> ExceptT (WriterT (return (f $ runWriter $ s)))))


