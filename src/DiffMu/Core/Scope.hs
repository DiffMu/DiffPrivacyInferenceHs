
module DiffMu.Core.Scope where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC

import qualified Data.HashMap.Strict as H

import Debug.Trace

-- Definition of the typechecking scope

-- A scope with variables of type `v`, and contents of type `a` is simply a hashmap.
type Scope v a = H.HashMap v a

-- The default scope is an empty scope.
instance Default (Scope v a) where
  def = H.empty

-- Given a scope and a variable name v, we pop the topmost element from the list for v.
popDefinition :: (MonadDMTC t, DictKey v, Show v) => Scope v a -> v -> t (a, Scope v a)
popDefinition scope v =
  do d <- case H.lookup v scope of
                 Just x  -> return x
                 Nothing -> throwError (VariableNotInScope v)

     return (d, H.delete v scope) -- TODO

-- Given a scope, a variable name v , and a DMTerm t, we push t to the list for v.
pushDefinition :: (MonadDMTC t) => DMScope -> Symbol -> DMTerm -> t DMScope
pushDefinition scope v term = do
   tt <- substituteScope scope term
   return (H.insert v tt scope)


-- Our scopes have symbols as variables, and contain DMTerms.
type DMScope = Scope Symbol DMTerm

-- All hashmaps are `DictLike`
instance (DictKey k) => DictLike k v (H.HashMap k v) where
  setValue v m (h) = (H.insert v m h)
  deleteValue v (h) = (H.delete v h)
  getValue k (h) = h H.!? k

-- whenever we encounter an assignment, we replace every occurance of the assignee variable with
-- the term it is assigned to, except inside lambdas, where variables are only resolved once the
-- lam is applied to simething.
substituteScope :: (MonadDMTC t) => DMScope -> DMTerm -> t DMTerm
substituteScope scope term = let
      sub = substituteScope scope
   in do
      case term of
         Lam _ _ -> return term
         LamStar _ _ -> return term
         Choice _ -> return term
         Sng _ _ -> return term
         Arg _ _ -> return term

         Var vs τ -> case H.lookup vs scope of
                           Just t -> return t --TODO what about vt
                           _ -> throwError (VariableNotInScope vs)

         Ret t -> Ret <$> sub t
         Op op ts -> Op op <$> (mapM (sub) ts)
         Phi tc ti te -> Phi <$> (sub tc) <*> (sub ti) <*> (sub te)
         Apply tf ts -> Apply <$> (sub tf) <*> (mapM (sub) ts)
         Iter t1 t2 t3 -> Iter <$> (sub t1) <*> (sub t2) <*> (sub t3)
         FLet fname jτs ft body -> FLet fname jτs <$> (sub ft) <*> (sub body)
         Tup ts -> Tup <$> (mapM (sub) ts)
         Gauss r e d f -> Gauss <$> (sub r) <*> (sub e) <*> (sub d) <*> (sub f)

         SLet v t body -> let vname = fstA v in
                              case H.member vname scope of -- does v exist in scope already?
                                 True -> do -- if so:
                                    newname <- uniqueName vname -- create a new name for v
                                    -- rename all occurances of v in the body with newname before substituting.
                                    SLet (newname :- (sndA v)) <$> (sub t) <*> (sub (rename vname newname body))
                                 False -> SLet v <$> (sub t) <*> (sub body) -- else just substitute ahead.
         TLet vs t body ->  case any (\v -> H.member (fstA v) scope) vs of -- is one of the assignees in scope?
                                 True -> do -- if so:
                                            let k = intersect (map fstA vs) (H.keys scope) -- get the names of all of them
                                            newvs <- mapM uniqueName k -- create a new name for each
                                            -- rename all occurances of all names in k in the body into their respective new names.
                                            let newbody = foldl (\b -> \(v, newv) -> rename v newv b) body (zip k newvs)
                                            TLet vs <$> (sub t) <*> (sub newbody) -- then substitute.
                                 False -> TLet vs <$> (sub t) <*> (sub body)


uniqueName :: (MonadDMTC t) => Symbol -> t Symbol
uniqueName s = return (s <> (Symbol "_unique")) -- TODO do this properly

-- rename olds with news in term, whenever it is not overloaded.
rename :: Symbol -> Symbol -> DMTerm -> DMTerm
rename olds news term =
   let re = rename olds news in
      case term of
         Sng _ _ -> term
         Arg _ _ -> term

         Var s τ -> if s == olds
            then Var news τ -- variable sold gets renamed.
            else term

         Ret t -> re t
         Op op ts -> Op op (re <$> ts)
         Phi tc ti te -> Phi (re tc) (re tc) (re tc)
         FLet fname jτs ft body -> FLet fname jτs (re ft) (re body)
         Choice cs -> Choice (H.map re cs)
         Apply t ts -> Apply (re t) (re <$> ts)
         Iter t1 t2 t3 -> Iter (re t1) (re t2) (re t3)
         Tup ts -> Tup (re <$> ts)
         Gauss r e d f -> Gauss (re r) (re e) (re d) (re f)

         Lam xτs body -> case olds `elem` (map fstA xτs) of
                                     True -> term -- we don't rename the function argument variable.
                                     False -> Lam xτs (re body)
         LamStar xτs body -> case olds `elem` (map fstA xτs) of
                                     True -> term -- we don't rename the function argument variable.
                                     False -> LamStar xτs (re body)

         SLet s r body -> if (fstA s) == olds
                             then SLet s (re r) body -- don't rename in the body if this slet overwrites olds
                             else SLet s (re r) (re body)
         TLet vs t body -> case olds `elem` (map fstA vs) of
                                True -> TLet vs (re t) body
                                False -> TLet vs (re t) (re body)
