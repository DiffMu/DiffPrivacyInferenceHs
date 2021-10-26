
module DiffMu.Typecheck.Preprocess.FLetReorder where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Core.Logging
import DiffMu.Typecheck.Operations
import DiffMu.Core.DelayedScope
import DiffMu.Typecheck.JuliaType
import DiffMu.Typecheck.Constraint.IsFunctionArgument
import DiffMu.Typecheck.Constraint.IsJuliaEqual
import DiffMu.Typecheck.Constraint.CheapConstraints
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T

import Debug.Trace

type FLetTC = LightTC Location_PrePro_FLetReorder ()

findDuplicates :: Eq a => [a] -> [a]
findDuplicates = findDuplicates' []
  where
    findDuplicates' :: Eq a => [a] -> [a] -> [a]
    findDuplicates' good [] = []
    findDuplicates' good (a:as) = case a `elem` good of
      False -> findDuplicates' (a:good) as
      True  -> a : findDuplicates' (good) as

collectAllFLets :: DMTerm -> FLetTC DMTerm
collectAllFLets (FLet var def rest) = do
  let FindFLetsResult defs rest' = findFLets var rest
      alldefs = (def:defs)

  -- we derive the julia type from the term, appending the corresponding julia types to their definitions
  allsigs <- mapM getJuliaSig alldefs

  -- we search for duplicate signatures,
  -- if there are any, we throw an error
  case findDuplicates allsigs of
    [] -> pure ()
    xs -> throwError $ FLetReorderError $ "The function `" <> show var <> "` has more than one definition for the following signatures: " <> show xs <> "\nThis means that the earlier definitions are going to have no effect, and as a precaution this is not allowed."

  -- let alldefsWithJuliaSig = zip allsigs alldefs
      -- we thread the elements through a hashmap => if we have terms with the same juliatype,
      -- the second one overwrites the first one
  --     alldefsWithJuliaSig' = H.elems (H.fromList alldefsWithJuliaSig)
  -- logForce $ "-----------------"
  -- logForce $ "for var " <> show var <> " found the signatures:"
  -- logForce $ show alldefsWithJuliaSig
  -- logForce $ "after removing duplicates, we have: "
  -- logForce $ show alldefsWithJuliaSig'

  updatedAllDefs <- mapM collectAllFLets alldefs
  updatedRest <- collectAllFLets rest'
  return $ expandFLets var updatedAllDefs updatedRest
collectAllFLets (SLet var def rest) = SLet var <$> (collectAllFLets def) <*> (collectAllFLets rest)
collectAllFLets (TLet var def rest) = TLet var <$> (collectAllFLets def) <*> (collectAllFLets rest)
collectAllFLets (Extra e)  = pure $ Extra undefined

collectAllFLets rest = recDMTermMSameExtension collectAllFLets rest


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
findFLets target (BBLet var args rest) = let FindFLetsResult others rest' = findFLets target rest
                                         in FindFLetsResult (others) (BBLet var args rest')
findFLets target t = FindFLetsResult [] t


getJuliaSig :: DMTerm -> LightTC l s JuliaSig
getJuliaSig (Lam as _) = pure $ map sndA as
getJuliaSig (LamStar as _) = pure $ map (fst . sndA) as
getJuliaSig _ = impossible "Expected a lam/lamstar inside an flet."

