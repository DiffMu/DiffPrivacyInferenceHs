
module Spec.Base
  (module All
  , tc , tcl , tcb , sn , sn_EW
  )
where

import DiffMu.Prelude as All
import DiffMu.Abstract as All
import DiffMu.Core as All
import DiffMu.Core.TC as All
import DiffMu.Core.Logging as All
import DiffMu.Core.Definitions as All
import DiffMu.Core.Symbolic as All
import DiffMu.Core.Context as All
import DiffMu.Core.DelayedScope as All
import DiffMu.Typecheck.Operations as All
import DiffMu.Typecheck.Subtyping as All
import DiffMu.Typecheck.Typecheck as All
import DiffMu.Typecheck.Constraint.IsJuliaEqual as All
import DiffMu.Runner as All
import DiffMu.Parser.DMTerm.FromString as All

import DiffMu.Typecheck.JuliaType as All

import Algebra.PartialOrd as All

import           Foreign.C.String as All

import Debug.Trace as All


import Test.Hspec as All
import Test.Hspec.Core.Runner as All


tc :: TC a -> IO (Either DMException a)
tc r = do
  -- NOTE: This is necessary to have deterministic typechecking calls
  reset_tevar_counter
  --

  x <- executeTC (DontShowLog) r
  return (fst <$> x)

tcl :: TC a -> IO (Either DMException a)
tcl r = do
  -- NOTE: This is necessary to have deterministic typechecking calls
  reset_tevar_counter
  --

  x <- executeTC (DoShowLog Force [Location_Constraint , Location_INC, Location_MonadicGraph]) r
  -- x <- executeTC (DoShowLog Force [Location_Constraint, Location_Subtyping]) r
  return (fst <$> x)


tcb :: Bool -> TC a -> IO (Either DMException a)
tcb True = tcl
tcb False = tc

sn :: Normalize TC a => TC a -> TC a
sn x = do
  x' <- x
  solveAllConstraints [SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal]
  normalize x'

sn_EW :: Normalize TC a => TC a -> TC a
sn_EW x = do
  x' <- x
  solveAllConstraints [SolveExact,SolveAssumeWorst]
  normalize x'


