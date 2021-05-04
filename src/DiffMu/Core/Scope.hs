
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

-- Our scopes have symbols as variables, and contain DMTerms and the scope in which the variable
-- ought to be checked, i.e. the scope that was current during 
newtype DMScope = DMScope (Scope Symbol (DMTerm, DMScope))
   deriving (Show)

-- typechecking actually carries two scopes, where the first one is the toplevel scope where nothing
-- is ever popped, and the second that get's replaced by the one stored inside a Var terms entry
-- upon encountering the Var term. the only time where the toplevel scope is used for checking is in
-- Lam and LamStar terms, which are checked in the scope current during application, not during devlaration.
-- this reflects julia runtime behaviour.
type DMScopes = (DMScope, DMScope)

-- The default scope is an empty scope.
instance Default (Scope v a) where
  def = H.empty

instance Default DMScope where
  def = DMScope def



-- Given a scope and a variable name v, we pop the topmost element from the list for v.
popDefinition :: MonadDMTC t => DMScopes -> Symbol -> t (DMTerm, DMScopes)
popDefinition (DMScope topscope, DMScope varscope) v = do
   traceM "popping"
   traceM (show v)
   case H.lookup v varscope of
      Just (x, (DMScope vvarscope))  -> return (x, (DMScope topscope, DMScope (H.delete v vvarscope)))
      Nothing -> throwError (VariableNotInScope v)

-- Given a scope, a variable name v , and a DMTerm t, we push t to the list for v.
pushDefinition :: (MonadDMTC t) => DMScopes -> Symbol -> DMTerm -> t DMScopes
pushDefinition (DMScope topscope, DMScope varscope) v term = do
   let entry = (term, (DMScope topscope))
   return (DMScope (H.insert v entry topscope), DMScope (H.insert v entry varscope))

pushChoice :: (MonadDMTC t) => DMScopes -> Symbol -> [JuliaType] -> DMTerm -> t DMScopes
pushChoice scope fname sign term = do
   let (DMScope topscope, DMScope varscope) = scope
   scope' <- case (H.lookup fname varscope) of
                  Nothing -> pushDefinition scope fname (Choice (H.singleton sign term)) -- if there are no other methods just push
                  Just (Choice d, _) -> do -- else append the method to the Choice term
                                        (_, scope'') <- popDefinition scope fname
                                        pushDefinition scope'' fname (Choice (H.insert sign term d))
                  _ -> throwError (ImpossibleError "Invalid scope entry.")
   return scope'

-- All hashmaps are `DictLike`
instance (DictKey k) => DictLike k v (H.HashMap k v) where
  setValue v m (h) = (H.insert v m h)
  deleteValue v (h) = (H.delete v h)
  getValue k (h) = h H.!? k

-- whenever we encounter an assignment, we replace every occurance of the assignee variable with
-- the term it is assigned to, except inside lambdas, where variables are only resolved once the
-- lam is applied to simething.

uniqueName :: (MonadDMTC t) => Symbol -> t Symbol
uniqueName s = return (s <> (Symbol "_unique")) -- TODO do this properly

-- rename olds with news in term, whenever it is not overloaded.
rename :: Symbol -> Symbol -> DMTerm -> DMTerm
rename olds news term =
   let re = rename olds news in
      case term of
         Sng _ _ -> term
         Arg _ _ _ -> term

         Var s τ -> if s == olds
            then Var news τ -- variable sold gets renamed.
            else term

         Ret t -> re t
         Op op ts -> Op op (re <$> ts)
         Phi tc ti te -> Phi (re tc) (re tc) (re tc)
         FLet fname jτs ft body -> FLet fname jτs (re ft) (re body)
         Choice cs -> Choice (H.map re cs)
         Apply t ts -> Apply (re t) (re <$> ts)
         Tup ts -> Tup (re <$> ts)
         Gauss r e d f -> Gauss (re r) (re e) (re d) (re f)
         MCreate n m bf -> MCreate (re n) (re m) (re bf)
         ClipM c m -> ClipM c (re m)
         Iter t1 t2 t3 -> Iter (re t1) (re t2) (re t3)
         Loop it cs (x1, x2) b -> case olds `elem` [x1, x2] of
                                     True -> Loop (re it) (re cs) (x1, x2) b
                                     False -> Loop (re it) (re cs) (x1, x2) (re b)

         Lam xτs body -> case olds `elem` (map fstA xτs) of
                                     True -> term -- we don't rename the function argument variable.
                                     False -> Lam xτs (re body)
         LamStar xτs body -> case olds `elem` (map (\x -> fstA (fst x)) xτs) of
                                     True -> term -- we don't rename the function argument variable.
                                     False -> LamStar xτs (re body)

         SLet s r body -> if (fstA s) == olds
                             then SLet s (re r) body -- don't rename in the body if this slet overwrites olds
                             else SLet s (re r) (re body)
         TLet vs t body -> case olds `elem` (map fstA vs) of
                                True -> TLet vs (re t) body
                                False -> TLet vs (re t) (re body)
