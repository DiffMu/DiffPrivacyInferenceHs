
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations

import qualified Data.HashMap.Strict as H

import Debug.Trace




------------------------------------------------------------------------
-- The typechecking function

--------------------
-- Sensitivity terms

checkSens :: DMTerm -> DMScope -> TC DMType

-- TODO: Here we assume that η really has type τ, and do not check it. Should maybe do that.
checkSens (Sng η τ) scope  = pure $ Numeric (Const (constCoeff (Fin η)) (createDMTypeNum τ))

-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms
checkSens (Arg x dτ) scope = do τ <- createDMType dτ
                                setVar x (τ :@ constCoeff (Fin 1))
                                return τ

checkSens (Var x dτ) scope = do -- get the term that corresponds to this variable from the scope dict
                                (vt, scope') <- popDefinition scope x

                                -- check the term in the new, smaller scope'
                                τ <- checkSens vt scope'

                                case dτ of
                                  JTAny -> return τ
                                  dτ -> do
                                    -- if the user has given an annotation
                                    -- inferred type must be a subtype of the user annotation
                                    dτd <- createDMType dτ
                                    addConstraint (Solvable (IsLessEqual (τ, dτd) ))
                                    return τ

-- typechecking an op
checkSens (Op op args) scope =
  -- We create a helper function, which infers the type of arg, unifies it with the given τ
  -- and scales the current context by s.
  let checkOpArg (arg,(τ,s)) = do
        τ_arg <- checkSens arg scope
        unify (Numeric τ) τ_arg
        mscale (svar s)
  in do
    -- We get create a new typeop constraint for op
    (res,arg_sens) <- makeTypeOp op (length args)

    -- We call our helper function `checkOpArg` on the argument-terms, zipped with the
    -- type(variables), sensitivities returned by `makeTypeOp`
    _ <- msum ((checkOpArg <$> (zip args arg_sens)))

    -- We return the `res` type given by `makeTypeOp`
    return (Numeric res)

checkSens (Phi cond ifbr elsebr) scope =
   let mcond = do
        τ_cond <- checkSens cond scope
        mscale (constCoeff Infty)
        return τ_cond
   in do
      τ_sum <- msum [(checkSens ifbr scope), (checkSens elsebr scope), mcond]
      (τif, τelse) <- case τ_sum of
                           (τ1 : τ2 : _) -> return (τ1, τ2)
                           _ -> throwError (ImpossibleError "Sum cannot return empty.")
      τ <- newVar
      addConstraint (Solvable (IsSupremum (τ, τif, τelse)))
      return τ

checkSens (Lam (Lam_ xτs body)) scope = do

  -- put a special term to mark x as a function argument. those get special tratment
  -- because we're interested in their sensitivity
  let scope' = mconcat ((\(x :- τ) -> setValue x (Arg x τ)) <$> xτs) scope

  τr <- checkSens body scope'
  xrτs <- getArgList xτs
  return (xrτs :->: τr)

checkSens (SLet (x :- dτ) term body) scope = do

  -- TODO this requires saving the annotation in the dict.
  case dτ of
     JTAny -> return dτ
     dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

  -- we're very lazy, only adding the new term for v to its scope entry
  scope' <- pushDefinition scope x term

  --check body, this will put the seinsitivity it has in the arguments in the monad context.
  τ <- checkSens body scope'
  return τ


checkSens (Apply f args) scope = let
   -- check a single argument, scale its context with the corresponding sensitivity variable
   checkFArg :: DMTerm -> Sensitivity -> TC DMType
   checkFArg arg s = do
      τ <- checkSens arg scope
      mscale s
      return τ
   in do
      svars :: [Sensitivity] <- mapM (\x -> newVar) args -- create an svar for each argument
      let margs = zipWith checkFArg args svars -- check args and scale with their respective svar

      let mf = checkSens f scope -- check function term

      τ_sum <- msum (mf : margs) -- sum args and f's context
      (τ_lam, argτs) <- case τ_sum of
                             (τ : τs) -> return (τ, (zipWith (:@) τs svars))
                             [] -> throwError (ImpossibleError "Sum cannot return empty list.")

      τ_ret <- newVar -- a type var for the function return type
      addConstraint (Solvable (IsLessEqual (τ_lam, (argτs :->: τ_ret)))) -- f's type must be subtype of an arrow matching arg types.
      return τ_ret


checkSens (FLet fname sign term body) scope = do

  -- make a Choice term to put in the scope
   scope' <- case (H.lookup fname scope) of
                  Nothing -> pushDefinition scope fname (Choice (H.singleton sign term))
                  Just (Choice d) -> do
                                        (_, scope'') <- popDefinition scope fname
                                        pushDefinition scope'' fname (Choice (H.insert sign term d))
                  _ -> throwError (ImpossibleError "Invalid scope entry.")

   -- check body with that new scope. Choice terms will result in IsChoice constraints upon ivocation of fname
   result <- checkSens body scope'
   _ <- removeVar @Sensitivity fname
   return result


checkSens (Choice d) scope = let
      checkChoice :: DMTerm -> TC DMType
      checkChoice t = do
         τ <- checkSens t scope
         flag <- newSVar "chflag"
         _ <- mscale (svar flag)
         return τ
      in do

         dd <- mapM checkChoice d
         τ <- newVar
         addConstraint (Solvable (IsChoice (τ, dd)))
         return τ

checkSens (Tup ts) scope = do
   τs <- msum (DiffMu.Prelude.map (\t -> (checkSens t scope)) ts)
   return (DMTup τs)


-- Everything else is currently not supported.
checkSens t scope = throwError (UnsupportedTermError t)


--------------------------------------------------------------------------------
-- Privacy terms

checkPriv :: DMTerm -> DMScope -> TC DMType

checkPriv (Ret t) scope = do
   throwError (ImpossibleError "?!")
--   τ <- checkSens t scope
--   _ <- truncate(∞)
--   return τ -- TODO truncate to inf

checkPriv (SLet (x :- dτ) term body) scope =
  -- push x to scope, check body, and discard x from the result context.
  -- this is the bind rule; as we expect the body to be a privacy term we don't need to worry about x's sensitivity
  let mbody = do
         scope' <- pushDefinition scope x (Arg x dτ)
         τ <- checkPriv body scope'
         _ <- removeVar @Privacy x
         return τ
  in do
     -- TODO this requires saving the annotation in the dict.
     case dτ of
          JTAny -> return dτ
          dτ -> throwError (ImpossibleError "Type annotations on variables not yet supported.")

     sum <- msum [mbody, (checkPriv term scope)]
     res <- case sum of
                    [τ::DMType,_] -> return τ
                    _ -> throwError (ImpossibleError "?!")

     return res

checkPriv t scope = checkPriv (Ret t) scope


-------------------------------------------------------------
-- Definition of the scope

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
pushDefinition :: (MonadDMTC t) => DMScope -> Symbol -> DMTerm-> t DMScope
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

substituteScope :: (MonadDMTC t) => DMScope -> DMTerm -> t DMTerm
substituteScope scope term = let
      sub = substituteScope scope
   in do
      case term of
         Lam _ -> return term
         LamStar _ -> return term
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
uniqueName s = return (Symbol "unique") -- TODO do this properly

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

         Lam (Lam_ xτs body) -> case olds `elem` (map fstA xτs) of
                                     True -> term -- we don't rename the function argument variable.
                                     False -> Lam (Lam_ xτs (re body))
         LamStar (Lam_ xτs body) -> case olds `elem` (map fstA xτs) of
                                     True -> term -- we don't rename the function argument variable.
                                     False -> LamStar (Lam_ xτs (re body))

         SLet s r body -> if (fstA s) == olds
                             then SLet s (re r) body -- don't rename in the body if this slet overwrites olds
                             else SLet s (re r) (re body)
         TLet vs t body -> case olds `elem` (map fstA vs) of
                                True -> TLet vs (re t) body
                                False -> TLet vs (re t) (re body)
