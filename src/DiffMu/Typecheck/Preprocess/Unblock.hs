{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.Unblock where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Typecheck.Preprocess.Common

import Debug.Trace

-----------------------------------------------------------------------------------
-- preprocessing step to make procedural "blocks" of statements into nice nested DMTerms.
-- 

type BlockTC = LightTC Location_PrePro_Demutation ()


unblock :: DemutDMTerm -> BlockTC DMTerm
unblock pt = case pt of
    Extra (DemutBlock []) -> internalError $ "empty block"
    Extra (DemutBlock [b]) -> unblock b
    Extra (DemutBlock (b:bs)) -> unlistM (unblock b) bs
    Extra _ -> internalError $ "found a DemutDMTerm (that's not a block) where a DMTerm or block was expected: " <> show pt
    _ -> recDMTermM unblock (\x -> unblock (Extra x)) pt
    

unlistM :: BlockTC DMTerm -> [DemutDMTerm] -> BlockTC DMTerm
unlistM mlast mxs = let
      unlist :: DMTerm -> [DemutDMTerm] -> BlockTC DMTerm
      unlist last [] = return last
      unlist last ((Extra (DemutBlock bs)) : xs) = unlistM (unlist last bs) xs
      unlist last ((Extra (DemutPhi c [t,f])) : xs) = unlistM (Phi <$> (unblock c) <*> (unlist last [t]) <*> (unlist last [f])) xs
      unlist last ((Extra (DemutPhi c [t])) : xs) = unlistM (Phi <$> (unblock c) <*> (unlist last [t]) <*> pure last) xs
      unlist last ((Extra (DemutPhi c bs)) : xs) = internalError $ "wrong number of branches in DemutPhi: " <> show bs
      unlist last ((Extra (DemutSLetBase k a b)) : xs) = unlistM (SLetBase k a <$> (unblock b) <*> pure last) xs
      unlist last ((Extra (DemutTLetBase k a b)) : xs) = unlistM (TLetBase k a <$> (unblock b) <*> pure last) xs
      unlist last ((Extra (DemutFLet a b)) : xs) = unlistM (FLet a <$> (unblock b) <*> pure last) xs
      unlist last ((Extra (DemutBBLet a b)) : xs) = unlist (BBLet a b last) xs
      unlist last ((Extra (DemutLoop n cvars it body)) : xs) =
             unlistM (TLet [Just s :- JTAny | s <- cvars] <$> (Loop <$> (unblock n) <*> pure cvars <*> pure it <*> (unblock body)) <*> pure last) xs
      unlist last (x:xs) = internalError $ "found a DMTerm where a DemutDMTerm was expected:" <> show x
   in join $ unlist <$> mlast <*> (pure mxs)

