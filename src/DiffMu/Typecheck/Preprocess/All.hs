
module DiffMu.Typecheck.Preprocess.All where

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
  logForce $ "-----------------------------------"
  logForce $ "Toplevel information:\n" <> show tlinfo

  -- -- mutation processing
  term'' <- liftLightTC (MFull def def tlinfo) (\_ -> ()) (demutate term')
  -- term'' <- liftLightTC () (\_ -> ()) (nondemutate term')

  -- flet processing
  term''' <- liftLightTC def def (collectAllFLets term'')

  logForce $ "-----------------------------------"
  logForce $ "FLet processed term:\n" <> showPretty term'''

  -- lexical scoping processing
  -- term'''' <- liftLightTC (LSFull def) (\_ -> ()) (processLS term''')

  -- done
  return term'''

