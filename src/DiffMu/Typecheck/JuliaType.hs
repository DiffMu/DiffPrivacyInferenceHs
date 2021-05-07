{-# LANGUAGE OverloadedLists #-}

module DiffMu.Typecheck.JuliaType where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core.Definitions
import DiffMu.Core.TC
import DiffMu.Core.Symbolic
import DiffMu.Typecheck.Subtyping

import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict (HashMap)
import qualified Data.POSet as PO
import Data.POSet (POSet)

-- local imports
import Algebra.PartialOrd

import Data.IORef
import System.IO.Unsafe

import           Foreign.C.String
import           Foreign.C.Types
import           Foreign.Ptr
import           Foreign.Marshal.Unsafe

import Debug.Trace


juliatypes :: DMTypeOf k -> [JuliaType]
juliatypes (Numeric (Const _ τ)) = juliatypes τ
juliatypes (Numeric (NonConst τ)) = juliatypes τ
juliatypes (Numeric (TVar x)) = [JTNumInt, JTNumReal]
juliatypes DMInt = [JTNumInt]
juliatypes DMReal = [JTNumReal]
juliatypes (Const _ τ) = juliatypes τ
juliatypes (NonConst τ) = juliatypes τ
-- TODO: This is not like in DM.jl, and another workaround should be found!
juliatypes (TVar x) = [JuliaType "Union{}"]
juliatypes (_ :->: _) = [JuliaType "Function"]
juliatypes (_ :->*: _) = [JuliaType "Function"]
juliatypes (DMTup xs) =
  let jss :: [[JuliaType]]
      jss = juliatypes `mapM` xs
      jss' :: [[String]]
      jss' = fmap (\(JuliaType j) -> j) <$> jss
      f js = JuliaType $ "Tuple{" <> intercalate ", " js <> "}"
  in f <$> jss'
juliatypes (Fun _) = [JuliaType "Function"]
juliatypes (NoFun τ) = juliatypes (fstAnn τ)
juliatypes (Trunc _ τ) = juliatypes τ
juliatypes (TruncFunc _ τ) = juliatypes τ
juliatypes (_ :↷: τ) = juliatypes τ
juliatypes τ = error $ "juliatypes(" <> show τ <> ") not implemented."

global_callback_issubtype :: IORef (DMEnv)
global_callback_issubtype = unsafePerformIO (newIORef makeEmptyDMEnv)

instance PartialOrd JuliaType where
  leq (JuliaType a) (JuliaType b) =
    let callback = (askJuliaSubtypeOf $ unsafePerformIO (readIORef global_callback_issubtype))
    in case (callback) of
      Nothing -> error "Julia callback (issubtype) is not set."
      Just fun  -> unsafeLocalState (withCString a (\ca -> withCString b (\cb -> return $ call_StringStringBool fun ca cb)))
      -- Just f  -> call_StringStringBool f t s


foreign import ccall "dynamic" call_StringStringBool :: FunPtr (CString -> CString -> Bool) -> CString -> CString -> Bool


--instance Solve MonadDMTC IsChoice (DMType, (HashMap [JuliaType] (DMType , Sensitivity))) where
--  solve_ Dict _ name (IsChoice arg) = solveIsChoice name arg
type ChoiceHash = HashMap [JuliaType] ((DMFun :& Sensitivity), Sensitivity)

instance Solve MonadDMTC IsChoice ([DMFun :& Sensitivity], ChoiceHash) where
  solve_ Dict _ name (IsChoice arg) = pure ()

solveIsChoice :: forall t. IsT MonadDMTC t => Symbol -> ([DMFun :& Sensitivity], ChoiceHash) -> t ()
solveIsChoice name (required, provided) = do
   -- remove all choices from the "required" list that have a unique match in the "provided" hashmap.
   -- when a choice is resolved, the corresponding counter in the hashmap is incremented by one.
   let matchArgs ::  [DMFun :& Sensitivity] -> ChoiceHash -> t ([DMFun :& Sensitivity], ChoiceHash)
       matchArgs curReq curProv = do
          case curReq of
             [] -> return ([], curProv)
             (τs : restReq) -> do -- go through all required methods
                 case fstAnn τs of
                      TVar _ -> do -- it was a tvar
                                   (resR, resP) <- (matchArgs restReq curProv) -- can't resolve TVar choice, keep it and recurse.
                                   return ((τs : resR), resP)
                      τsτ -> do
                              -- get methods that could be a match, and free TVars in the args while we're at it
                              (candidates, hasFreeVars) <- case τsτ of
                                  args :->: _  -> do
                                                    -- remove all methods that definitely don't match this signature
                                                    let cand = (H.filterWithKey (\s c -> choiceCouldMatch args s) provided)
                                                    -- filter all argument types that would be "Function" in julia...
                                                    let argsNoFun = filter (\τa -> case τa of {Fun _ -> False; _ -> True}) args
                                                    -- ... and get the free typevars of the rest.
                                                    let free = and (null . freeVars @_ @TVarOf <$> argsNoFun)
                                                    return (cand, free)
                                  args :->*: _ -> do -- same as for the above case.
                                                    let cand = (H.filterWithKey (\s c -> choiceCouldMatch args s) provided)
                                                    let argsNoJFun = filter noJuliaFunction args
                                                    let free = and (null . freeVars @_ @TVarOf <$> argsNoJFun)
                                                    return (cand, free)
                                  _ -> throwError (ImpossibleError ("Invalid type for Choice: " <> show τsτ))

                              if H.null candidates
                                 then throwError (NoChoiceFoundError $ "No matching choice for " <> show τs <> " found in " <> show provided)
                                 else pure Nothing

                              -- if there is no free tyepevars in τs arguments, throw out methods that are more general than others
                              -- if we don't know all types we cannot do this, as eg for two methods
                              -- (Int, Int) => T
                              -- (Real, Number) => T
                              -- and arg types (TVar, DMInt), both methods are in newchoices, but if we later realize the TVar
                              -- is a DMReal, the first one does not match even though it's less general.
                              -- filter Fun arguments, as the all have the same type "Function" in julia/
                              let candidates' = case hasFreeVars of
                                    -- if no tvars are in the args
                                    True  -> keepLeastGeneral candidates
                                    -- else we do not change them
                                    False -> candidates

                              case length candidates' == length provided of
                                 -- no choices were discarded, the constraint could not be simplified.
                                 True -> do
                                            (resR, resP) <- (matchArgs restReq curProv) -- can't resolve choice, keep it and recurse.
                                            return ((τs : resR), resP)

                                 -- some choices were discarded, so we can continue
                                 False -> do
                                    case H.toList candidates' of
                                        -- only one left, we can pick that one yay
                                        -- even if there is free TVars, we don't have to add subtype constraints for the user-given signature,
                                        -- as it was encoded in the Arr type of the choice, so its arg types can only be refinements.
                                       [(sign, ((cτ :@ cs), count))] -> do
                                                                let (τ :@ s) = τs
                                                                cτ ⊑! τ -- set type to chosen method
                                                                let resP = H.insert sign ((cτ :@ cs), count +! s) curProv -- count up
                                                                matchArgs restReq resP -- discard entry by recursing without τs

                                       _ -> do -- more than one left, need to wait.
                                               (resR, resP) <- (matchArgs restReq curProv) -- can't resolve choice, keep it and recurse.
                                               return ((τs : resR), resP)


   (newcs, newdict) <- matchArgs required provided -- get new dict and list of yet unresolved choices.

   -- discard or update constraint.
   case newcs of
        [] -> do -- complete resolution! set counters, discard.
                mapM (\((_ :@ flag), count) -> flag ==! count) newdict
                dischargeConstraint name
        cs -> do -- still not all choices resolved, just kick the resolved ones out of the constraint.
                 -- their sensitivity is already included in their method's count.
                updateConstraint name (Solvable (IsChoice (newcs, newdict)))

   return ()

-- remove dict entries whose signature is supertype of some other signature.
-- this is only reasonable if the dmtype signature we're trying to match has no free variables,
-- bc then the minimal matching method is picked.
keepLeastGeneral :: ChoiceHash -> ChoiceHash
keepLeastGeneral cs =
  -- make a poset from the (julia-)subtype relations of the given signatures
  let pos :: POSet [JuliaType]
      pos = PO.fromList (HS.toList (H.keysSet cs))
      -- pick the ones that are not supertypes of any of the others
      mins = PO.lookupMin pos
      mins' = [(k, cs H.! k) | k <- mins]
  in H.fromList mins'

-- determine whether a function with the given dmtype signature could match a method with the given juliatype signature.
choiceCouldMatch :: forall e. (DMExtra e) => [DMTypeOf (AnnKind e)] -> [JuliaType] -> Bool
choiceCouldMatch args cs =
   case length args == length cs of
        False -> False
        True -> let couldMatch t c = or ((`leq` c) <$> juliatypes t)
                in (and (zipWith couldMatch args cs))


-- return False if this type would become a "Function" if converted to a julia type
noJuliaFunction :: forall e. (DMExtra e) => DMTypeOf (AnnKind e) -> Bool
noJuliaFunction τ = (juliatypes τ == [JuliaType "Function"])

