
module DiffMu.Typecheck.Preprocess where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations
import DiffMu.Core.DelayedScope
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.IsFunctionArgument
import DiffMu.Typecheck.Constraint.IsJuliaEqual
import DiffMu.Typecheck.Constraint.CheapConstraints

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace


preprocessDMTerm :: DMTerm -> DMTerm
preprocessDMTerm t = collectAllFLets t

collectAllFLets :: DMTerm -> DMTerm

collectAllFLets (FLet var def rest) =
  let FindFLetsResult defs rest' = findFLets var rest
  in FLet var (collectAllFLets def) (expandFLets var (collectAllFLets <$> defs) rest')
collectAllFLets (SLet var def rest) = SLet var (collectAllFLets def) (collectAllFLets rest)
collectAllFLets (TLet var def rest) = TLet var (collectAllFLets def) (collectAllFLets rest)

collectAllFLets (Ret t)           = Ret (collectAllFLets t)
collectAllFLets (Sng a t)         = Sng a t
collectAllFLets (Var a t)         = Var a t
collectAllFLets (Rnd t)           = Rnd t
collectAllFLets (Arg a b c)       = Arg a b c
collectAllFLets (Op o ts)         = Op o (collectAllFLets <$> ts)
collectAllFLets (Phi a b c)       = Phi (collectAllFLets a) (collectAllFLets b) (collectAllFLets c)
collectAllFLets (Lam a t)         = Lam a (collectAllFLets t)
collectAllFLets (LamStar a t)     = LamStar a (collectAllFLets t)
collectAllFLets (Apply t ts)      = Apply (collectAllFLets t) (collectAllFLets <$> ts)
collectAllFLets (Choice m)        = Choice (collectAllFLets <$> m)
collectAllFLets (Tup ts)          = Tup (collectAllFLets <$> ts)
collectAllFLets (Gauss a b c d)   = Gauss (collectAllFLets a) (collectAllFLets b) (collectAllFLets c) (collectAllFLets d)
collectAllFLets (MCreate a b x c) = MCreate (collectAllFLets a) (collectAllFLets b) x (collectAllFLets c)
collectAllFLets (Transpose a)     = Transpose (collectAllFLets a)
collectAllFLets (Index a b c)     = Index (collectAllFLets a) (collectAllFLets b) (collectAllFLets c)
collectAllFLets (ClipM x a)       = ClipM x (collectAllFLets a)
collectAllFLets (Iter a b c)      = Iter (collectAllFLets a) (collectAllFLets b) (collectAllFLets c)
collectAllFLets (Loop a b x c)    = Loop (collectAllFLets a) (collectAllFLets b) x (collectAllFLets c)

expandFLets :: TeVar -> [DMTerm] -> DMTerm -> DMTerm
expandFLets var [] rest = rest
expandFLets var (d:defs) rest = FLet var d (expandFLets var defs rest)

data FindFLetsResult = FindFLetsResult
  {
    otherDefinitions :: [DMTerm]
  , restOfTerm :: DMTerm
  }

findFLets :: TeVar -> DMTerm -> FindFLetsResult
findFLets target (FLet var def rest) | target == var = let FindFLetsResult others rest' = findFLets target rest
                                                       in FindFLetsResult (def:others) rest'
findFLets target (FLet var def rest) | otherwise     = let FindFLetsResult others rest' = findFLets target rest
                                                       in FindFLetsResult (others) (FLet var def rest')
findFLets target (SLet var def rest) = let FindFLetsResult others rest' = findFLets target rest
                                       in FindFLetsResult (others) (SLet var def rest')
findFLets target (TLet var def rest) = let FindFLetsResult others rest' = findFLets target rest
                                       in FindFLetsResult (others) (TLet var def rest')
findFLets target t = FindFLetsResult [] t




