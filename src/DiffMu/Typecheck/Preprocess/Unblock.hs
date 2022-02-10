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

unblockingError = throwError . UnblockingError

unblock :: DemutDMTerm -> BlockTC DMTerm
unblock = unblockValue


unblockValue :: DemutDMTerm -> BlockTC DMTerm
unblockValue (Extra e) = case e of
  DemutBlock []     -> unblockingError $ "Found an empty block where a value was expected."
  DemutBlock (x:xs) -> unblockStatementsM (unblockValue x) xs
  _                 -> unblockingError $ "Found a statement without return value. This is not allowed.\n" <> "Statement:\n" <> showPretty e
unblockValue t = recDMTermM unblockValue (\x -> unblock (Extra x)) t


unblockStatementsM :: BlockTC DMTerm -> [DemutDMTerm] -> BlockTC DMTerm
unblockStatementsM mlast xs = join $ unblockStatements <$> mlast <*> pure xs

unblockStatements :: DMTerm -> [DemutDMTerm] -> BlockTC DMTerm
unblockStatements last [] = pure last
unblockStatements last ((Extra (DemutBlock bs))             : xs) = unblockStatementsM (unblockStatements last bs) xs
unblockStatements last ((Extra (DemutPhi c t (Just f)))     : xs) = unblockStatementsM (Phi <$> (unblock c) <*> (unblockStatements last [t]) <*> (unblockStatements last [f])) xs
unblockStatements last ((Extra (DemutPhi c t Nothing))      : xs) = unblockStatementsM (Phi <$> (unblock c) <*> (unblockStatements last [t]) <*> pure last) xs
unblockStatements last ((Extra (DemutSLetBase k a b))       : xs) = unblockStatementsM (SLetBase k a <$> (unblock b) <*> pure last) xs
unblockStatements last ((Extra (DemutTLetBase k a b))       : xs) = unblockStatementsM (TLetBase k a <$> (unblock b) <*> pure last) xs
unblockStatements last ((Extra (DemutFLet a b))             : xs) = unblockStatementsM (FLet a <$> (unblock b) <*> pure last) xs
unblockStatements last ((Extra (DemutBBLet a b))            : xs) = unblockStatements (BBLet a b last) xs
unblockStatements last ((Extra (DemutLoop n cvars cvars' it body)) : xs) =
        unblockStatementsM (TLet [s :- JTAny | s <- cvars'] <$> (Loop <$> (unblock n) <*> pure cvars <*> pure it <*> (unblock body)) <*> pure last) xs

unblockStatements last (x                                   : xs) = unblockingError $ "Expected a statement, but encountered a term:"
                                                                                   <> showPretty x



