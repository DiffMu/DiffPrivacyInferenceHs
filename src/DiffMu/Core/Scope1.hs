
module DiffMu.Core.Scope1 where

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

-- type SimpleScope = Scope Symbol DMTerm

-- Our scopes have symbols as variables, and contain DMTerms and the scope in which the variable
-- ought to be checked, i.e. the scope that was current during 
-- newtype DMScope = DMScope (Scope Symbol (DMTerm, DMScope))

-- typechecking actually carries two scopes, where the first one is the toplevel scope where nothing
-- is ever popped, and the second that get's replaced by the one stored inside a Var terms entry
-- upon encountering the Var term. the only time where the toplevel scope is used for checking is in
-- Lam and LamStar terms, which are checked in the scope current during application, not during devlaration.
-- this reflects julia runtime behaviour.
-- type DMScope = (DMScope, DMScope)

-- The default scope is an empty scope.
instance Default (Scope v a) where
  def = H.empty

  {-
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


-- Given a scope and a variable name v, we pop the topmost element from the list for v.
popDefinition :: MonadDMTC t => DMScope -> Symbol -> t (DMTerm, DMScope)
popDefinition (DMScope varscope) v = do
   case H.lookup v varscope of
      Just (x, vvarscope)  -> return (x, (vvarscope))
      Nothing -> throwError (VariableNotInScope v)

-- Given a scope, a variable name v , and a DMTerm t, we push t to the list for v.
pushDefinition :: (MonadDMTC t) => DMScope -> Symbol -> DMTerm -> t DMScope
pushDefinition (DMScope varscope) v term = do
   let entry = (term, (DMScope varscope))
   return (DMScope (H.insert v entry varscope))

pushChoice :: (MonadDMTC t) => DMScope -> Symbol -> [JuliaType] -> DMTerm -> t DMScope
pushChoice scope fname sign term = do
   let (DMScope varscope) = scope
   scope' <- case (H.lookup fname varscope) of
                  Nothing -> pushDefinition scope fname (Choice (H.singleton sign term)) -- if there are no other methods just push
                  Just (Choice d, _) -> do -- else append the method to the Choice term
                                        (_, scope'') <- popDefinition scope fname
                                        pushDefinition scope'' fname (Choice (H.insert sign term d))
                  _ -> throwError (ImpossibleError "Invalid scope entry.")
   return scope'
-}
-- All hashmaps are `DictLike`
instance (DictKey k) => DictLike k v (H.HashMap k v) where
  setValue v m (h) = (H.insert v m h)
  deleteValue v (h) = (H.delete v h)
  getValue k (h) = h H.!? k
  emptyDict = H.empty


uniqueName :: (MonadDMTC t) => Symbol -> t Symbol
uniqueName s = return (s <> (Symbol "_unique")) -- TODO do this properly
