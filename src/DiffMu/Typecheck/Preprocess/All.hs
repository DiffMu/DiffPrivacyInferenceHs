
module DiffMu.Typecheck.Preprocess.All where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.TopLevel
import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.FLetReorder
import DiffMu.Typecheck.Preprocess.LexicalScoping

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace

type PreProTC = LightTC Location_PreProcess ()

preprocessAll :: MutDMTerm -> PreProTC (DMTerm)
preprocessAll term = do

  -- top level processing

  (tlinfo, term') <- liftLightTC def def (checkTopLevel term)
  info $ "-----------------------------------"
  info $ "Toplevel information:\n" <> show tlinfo

  -- -- mutation processing
  term'' <- liftLightTC (MFull def def tlinfo) (\_ -> ()) (demutate term')
  -- term'' <- liftLightTC () (\_ -> ()) (nondemutate term')

  -- flet processing
  term''' <- liftLightTC def def (collectAllFLets term'')

  info $ "-----------------------------------"
  info $ "FLet processed term:\n" <> showPretty term'''

  -- lexical scoping processing
  term'''' <- liftLightTC (LSFull def) (\_ -> ()) (processLS term''')

  info $ "-----------------------------------"
  info $ "Lexical scoping processed term:\n" <> showPretty term''''

  -- done
  return term''''

