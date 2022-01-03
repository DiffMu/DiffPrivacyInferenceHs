
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.LexicalScoping where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace

-----------------------------------------------------------------------------------
-- preprocessing step to make function argument names unique

data LSFull = LSFull
  {
    _termVarsOfLS :: NameCtx
  }

-- the monad keeping the state we require to generate unique names
type LSTC = LightTC Location_PrePro_Demutation LSFull

$(makeLenses ''LSFull)

-- generate unique new variables if it's not a Nothing...
newTeVarMaybe :: (MonadState LSFull m) => (Maybe TeVar) -> m (Maybe TeVar)
newTeVarMaybe (Just t) = Just <$> (newTeVarOfLS t)
newTeVarMaybe Nothing = return Nothing

-- generate unique new variables
newTeVarOfLS :: (MonadState LSFull m) => TeVar -> m (TeVar)
newTeVarOfLS hintVar = termVarsOfLS %%= (first GenTeVar . (newName (hint hintVar)))
  where
    hint (GenTeVar (Symbol x))   = x <> "_genls"
    hint (UserTeVar (Symbol x))  = x <> "_uls"

-- transform the dmterm to one where function argument names are unique
-- by generating new names for them and substituting all occurances in the body
processLS :: DMTerm -> LSTC (DMTerm)
processLS t = substituteNames H.empty t

-- in a dmterm, apply all variable name substitutions contained in the hashmap recursively.
substituteNames :: H.HashMap TeVar TeVar -> DMTerm -> LSTC DMTerm
substituteNames names term = let
    subIf c = case H.lookup c names of
                    Nothing -> c
                    Just newc -> newc
    subMaybe (x :- t) = case x of
                             Nothing -> (Nothing :- t)
                             Just xn -> (Just (subIf xn) :- t)
    subSame t = substituteNames names t
  in case term of
   -- function argument variables are renamed to sth unique and substituted in the body
   Lam args body -> do
       let argnames = [x | (x :- _) <- args]
       newnames <- mapM newTeVarMaybe argnames -- generate new names for all argument variables
       let names' = H.union (H.fromList (zip [n | Just n <- argnames] [n | Just n <- newnames])) names -- overwrite hashmap with new names
       newbody <- substituteNames names' body -- substitute new names in the body
       return (Lam [(x :- t) | (x, (_ :- t)) <- (zip newnames args)] newbody)
   LamStar args body -> do
       let argnames = [x | (x :- _) <- args]
       newnames <- mapM newTeVarMaybe argnames -- generate new names for all argument variables
       let names' = H.union (H.fromList (zip [n | Just n <- argnames] [n | Just n <- newnames])) names -- overwrite hashmap with new names
       newbody <- substituteNames names' body -- substitute new names in the body
       return (LamStar [(x :- t) | (x, (_ :- t)) <- (zip newnames args)] newbody)
   -- args/vars are simply substituted
   Arg x t r -> case H.lookup x names of
       Nothing -> return term
       Just name -> return (Arg name t r)
   Var ((Just x) :- t) -> case H.lookup x names of
       Nothing -> return term
       Just name -> return (Var ((Just name) :- t))
   BBLet x ts tail -> case H.lookup x names of
       Just _ -> internalError "black boxes should have unique names..."
       Nothing ->         BBLet x ts <$> subSame tail
   BBApply t args caps -> BBApply <$> subSame t <*> (mapM subSame args) <*> (return (map subIf caps))
   FLet f t tail ->       FLet (subIf f) <$> subSame t <*> subSame tail
   -- the following 2 are only ok bc i cannot modify names from outer scope
   SLetBase k (Just x :- t) body tail -> SLetBase k (Just (subIf x) :- t) <$> subSame body <*> subSame tail
   TLetBase k ns body tail -> TLetBase k (map subMaybe ns) <$> subSame body <*> subSame tail
   MCreate t1 t2 (x1, x2) t3 -> MCreate <$> subSame t1 <*> subSame t2 <*> return (subIf x1, subIf x2) <*> subSame t3
   Loop t1 cs (x1, x2) body -> Loop <$> subSame t1 <*> return (map subIf cs) <*> return (fmap subIf x1, subIf x2) <*> subSame body
   _ -> recDMTermMSameExtension (substituteNames names) term
