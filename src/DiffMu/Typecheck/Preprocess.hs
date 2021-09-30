
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


preprocessDMTerm :: DMTerm -> TC DMTerm
preprocessDMTerm t = collectAllFLets t

collectAllFLets :: DMTerm -> TC DMTerm

collectAllFLets (FLet var def rest) = do
  let FindFLetsResult defs rest' = findFLets var rest
      alldefs = (def:defs)

  -- we derive the julia type from the term, appending the corresponding julia types to their definitions
  allsigs <- mapM getJuliaSig alldefs
  let alldefsWithJuliaSig = zip allsigs alldefs

      -- we thread the elements through a hashmap => if we have terms with the same juliatype,
      -- the second one overwrites the first one
      alldefsWithJuliaSig' = H.elems (H.fromList alldefsWithJuliaSig)
  debug $ "-----------------"
  debug $ "for var " <> show var <> " found the signatures:"
  debug $ show alldefsWithJuliaSig
  debug $ "after removing duplicates, we have: "
  debug $ show alldefsWithJuliaSig'

  updatedAllDefs <- mapM collectAllFLets alldefsWithJuliaSig'
  updatedRest <- collectAllFLets rest'
  return $ expandFLets var updatedAllDefs updatedRest
collectAllFLets (SLet var def rest) = SLet var <$> (collectAllFLets def) <*> (collectAllFLets rest)
collectAllFLets (TLet var def rest) = TLet var <$> (collectAllFLets def) <*> (collectAllFLets rest)
collectAllFLets (Extra e)  = pure $ Extra undefined

collectAllFLets (Ret t)           = Ret <$> (collectAllFLets t)
collectAllFLets (Sng a t)         = pure $ Sng a t
collectAllFLets (Var (a :- t))    = pure $ Var (a :- t)
collectAllFLets (Rnd t)           = pure $ Rnd t
collectAllFLets (Arg a b c)       = pure $ Arg a b c
collectAllFLets (Op o ts)         = Op o <$> (mapM collectAllFLets ts)
collectAllFLets (Phi a b c)       = Phi <$> (collectAllFLets a) <*> (collectAllFLets b) <*> (collectAllFLets c)
collectAllFLets (Lam a t)         = Lam a <$> (collectAllFLets t)
collectAllFLets (LamStar a t)     = LamStar a <$> (collectAllFLets t)
collectAllFLets (Apply t ts)      = Apply <$> (collectAllFLets t) <*> (mapM collectAllFLets ts)
collectAllFLets (Choice m)        = Choice <$> (mapM collectAllFLets m)
collectAllFLets (Tup ts)          = Tup <$> (mapM collectAllFLets ts)
collectAllFLets (Gauss a b c d)   = Gauss <$> (collectAllFLets a) <*> (collectAllFLets b) <*> (collectAllFLets c) <*> (collectAllFLets d)
collectAllFLets (MCreate a b x c) = MCreate <$> (collectAllFLets a) <*> (collectAllFLets b) <*> pure x <*> (collectAllFLets c)
collectAllFLets (Transpose a)     = Transpose <$> (collectAllFLets a)
collectAllFLets (Index a b c)     = Index <$> (collectAllFLets a) <*> (collectAllFLets b) <*> (collectAllFLets c)
collectAllFLets (ClipM x a)       = ClipM x <$> (collectAllFLets a)
collectAllFLets (Loop a b x c)    = Loop <$> (collectAllFLets a) <*> (pure b) <*> pure x <*> (collectAllFLets c)
collectAllFLets (SubGrad a b)     = SubGrad <$> collectAllFLets a <*> collectAllFLets b
collectAllFLets (ConvertM t)      = ConvertM <$> collectAllFLets t
collectAllFLets (Reorder a t)     = Reorder a <$> collectAllFLets t
-- collectAllFLets (MutLet t s)      = MutLet <$> collectAllFLets t <*> collectAllFLets s

expandFLets :: TeVar -> [DMTerm] -> DMTerm -> DMTerm
expandFLets var [] rest = rest
expandFLets var (d:defs) rest = FLet var d (expandFLets var defs rest)

type JuliaSig = [JuliaType]

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


getJuliaSig :: DMTerm -> TC JuliaSig
getJuliaSig (Lam as _) = pure $ map sndA as
getJuliaSig (LamStar as _) = pure $ map (fst . sndA) as
getJuliaSig _ = impossible "Expected a lam/lamstar inside an flet."

