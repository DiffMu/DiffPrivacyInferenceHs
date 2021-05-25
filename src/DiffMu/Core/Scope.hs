
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

type SimpleScope = Scope Symbol DMTerm

-- Our scopes have symbols as variables, and contain DMTerms and the scope in which the variable
-- ought to be checked, i.e. the scope that was current during 
newtype DMScope = DMScope (Scope Symbol (DMTerm, DMScope))

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

mergeScopes :: DMScope -> Scope Symbol [DMTerm]
mergeScopes a = f a emptyDict
  where f :: DMScope -> Scope Symbol [DMTerm] -> Scope Symbol [DMTerm]
        f (DMScope scope) acc =
          let cur = (\(term,scope) -> [term]) <$> scope
              others = [mergeScopes other | (_ , (_ , other)) <- H.toList scope]
              all = cur:others
              merged = foldl (H.unionWith (<>)) emptyDict all
              unique = nub <$> merged
          in unique


instance Show DMScope where
  show scope = showWith "\n" f (mergeScopes scope) ""
    where f name termlist =
            let name' = show name <> " := "
                n = length name'
                terms' = intercalate (",\n" <> take n (repeat ' ')) (show <$> termlist)
            in name' <> terms'

instance ShowDict v k (Scope v k) where
  showWith comma merge (d) emptycase =
    let d' = H.toList d
    in case d' of
      [] -> emptycase
      _  -> intercalate comma ((\(k,v) -> merge k v) <$> d')


-- this is called when checking Var. it looks for the given symbol in the varscope.
-- if it does not exist, we get an error.
-- else, we also look for the symbol in the topscope. if it exists there, we need to overwrite
-- it with the value it has in its assigned scope. an example to clarify:
-- function scope(z)
--   y = 100
--   g(x) = x+y
--   y = g(z)    # -> we have to check g(x) with the topscope where y's entry is replaced by 100
--   g(z)
-- end
popDefinition :: MonadDMTC t => DMScopes -> Symbol -> t (DMTerm, DMScopes)
popDefinition (DMScope topscope, DMScope varscope) v = do
   case H.lookup v varscope of
      Just (x, vvarscope) -> do -- vvarscope becomes the new varscope.
         case x of
            Choice _ -> return (x, (DMScope topscope, vvarscope))
            _ -> case H.lookup v topscope of
                  Just (topv, DMScope topvscope) -> do -- v is in the topscope too
                     case H.lookup v topvscope of -- v was overwritten some time so it is in the scope it is assigned by topscope
                        Just entry -> return (x, (DMScope (H.insert v entry topscope), vvarscope))
                        Nothing -> return (x, (DMScope (H.delete v topscope), vvarscope))
                  Nothing -> return (x, (DMScope topscope, vvarscope))
      Nothing -> throwError (VariableNotInScope v) -- v was not in the varscope.

-- Given a scope, a variable name v , and a DMTerm t, we push t to the list for v.
pushDefinition :: (MonadDMTC t) => DMScopes -> Symbol -> DMTerm -> t DMScopes
pushDefinition (DMScope topscope, DMScope varscope) v term = do
   let entry = (term, (DMScope topscope))
   return (DMScope (H.insert v entry topscope), DMScope (H.insert v entry varscope))

pushChoice :: (MonadDMTC t) => DMScopes -> Symbol -> [JuliaType] -> DMTerm -> t DMScopes
pushChoice scope fname sign term = do
   let (_, DMScope varscope) = scope
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
  emptyDict = H.empty


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
