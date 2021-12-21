
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.LexicalScoping where

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

import qualified Data.HashMap.Strict as H

import qualified Data.Text as T
import Data.Foldable

import Debug.Trace


data LSFull = LSFull
  {
    _termVarsOfLS :: NameCtx
  }


type LSTC = LightTC Location_PrePro_Demutation LSFull

$(makeLenses ''LSFull)

newTeVarMaybe :: (MonadState LSFull m) => (Maybe TeVar) -> m (Maybe TeVar)
newTeVarMaybe (Just t) = Just <$> (newTeVarOfLS t)
newTeVarMaybe Nothing = return Nothing

-- new variables
newTeVarOfLS :: (MonadState LSFull m) => TeVar -> m (TeVar)
newTeVarOfLS hintVar = termVarsOfLS %%= (first GenTeVar . (newName (hint hintVar)))
  where
    hint (GenTeVar (Symbol x))   = x <> "_genls"
    hint (UserTeVar (Symbol x))  = x <> "_uls"

processLS :: DMTerm -> LSTC (DMTerm)
processLS t = substituteNames H.empty t

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
{-
  [Asgmt JuliaType] (PreDMTerm t)
  | LamStar [(Asgmt (JuliaType, Relevance))] (PreDMTerm t)
  | Arg TeVar JuliaType Relevance
  | Var (Asgmt JuliaType)
  | BBLet TeVar [JuliaType] (PreDMTerm t) -- name, arguments, tail
  | BBApply (PreDMTerm t) [(PreDMTerm t)] [TeVar] -- term containing the application, list of captured variables.
  | FLet TeVar (PreDMTerm t) (PreDMTerm t)
  | SLetBase LetKind (Asgmt JuliaType) (PreDMTerm t) (PreDMTerm t)
  | TLetBase LetKind [(Asgmt JuliaType)] (PreDMTerm t) (PreDMTerm t)
  | MCreate (PreDMTerm t) (PreDMTerm t) (TeVar, TeVar) (PreDMTerm t)
  | Loop (PreDMTerm t) [TeVar] (Maybe TeVar, TeVar) (PreDMTerm t)


  | Ret ((PreDMTerm t))
  | Sng Float JuliaType
  | Rnd JuliaType
  | Op DMTypeOp_Some [(PreDMTerm t)]
  | Phi (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
  | Apply (PreDMTerm t) [(PreDMTerm t)]
  | Choice (HashMap [JuliaType] (PreDMTerm t))
  | Tup [(PreDMTerm t)]
  | Gauss (PreDMTerm t) (PreDMTerm t) (PreDMTerm t) (PreDMTerm t)
-- matrix related things
  | ConvertM (PreDMTerm t)
  | Transpose (PreDMTerm t)
  | Size (PreDMTerm t) -- matrix dimensions, returns a tuple of two numbers
  | Length (PreDMTerm t) -- vector dimension, returns a number
  | Index (PreDMTerm t) (PreDMTerm t) (PreDMTerm t) -- matrix index
  | VIndex (PreDMTerm t) (PreDMTerm t) -- vector index
  | Row (PreDMTerm t) (PreDMTerm t) -- matrix row
  | ClipM Clip (PreDMTerm t)
  -- Loop (DMTerm : "Number of iterations") ([TeVar] : "Captured variables") (TeVar : "name of iteration var", TeVar : "name of capture variable") (DMTerm : "body")
-- Special NN builtins
  | SubGrad (PreDMTerm t) (PreDMTerm t)
  | ScaleGrad (PreDMTerm t) (PreDMTerm t) -- scale (a : Scalar) (g : Mutating Gradient)
-- Special Tuple terms
  | Reorder [Int] (PreDMTerm t)
  | TProject Int (PreDMTerm t)
-- Special Scope terms
  | LastTerm (PreDMTerm t)
  deriving (Generic)

pattern SLet a b c = SLetBase PureLet a b c
pattern SBind a b c = SLetBase BindLet a b c
pattern TLet a b c = TLetBase PureLet a b c
pattern TBind a b c = TLetBase BindLet a b c
pattern LLet a b c = TLetBase LoopLet a b c
-}
