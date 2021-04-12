
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.TC
import DiffMu.Typecheck.Operations

import Data.HashMap.Strict as H

import Debug.Trace



createDMTypeNum :: JuliaNumType -> DMTypeOf BaseNumKind
createDMTypeNum JTNumInt = DMInt
createDMTypeNum JTNumReal = DMReal

createDMType :: MonadDMTC e t => JuliaType -> t e (DMTypeOf MainKind)
createDMType (JTNum τ) = pure (Numeric (NonConst (createDMTypeNum τ))) -- NOTE: defaulting to non-const might or might not be what we want to do here.
createDMType JTAny = TVar <$> newTVar "any"


type Scope v a = HashMap v [a]
instance Default (Scope v a) where
  def = H.empty

type Scoped v a = State (Scope v a)
runScoped = runState

popDefinition :: (MonadDMTC e t, DictKey v, Show v) => Scope v a -> v -> t e (a, Scope v a)
popDefinition scope v =
  do (d,ds) <- case H.lookup v scope of
                 Just (x:xs) -> return (x,xs)
                 _           -> throwError (VariableNotInScope v)
     return (d, H.insert v ds scope)


type DMScope = Scope Symbol DMTerm

checkSens :: DMTerm -> DMScope -> STC DMType

-- TODO: Here we assume that η really has type τ, and do not check it.
--       Should probably do that.
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


checkSens (Op op args) scope =
  let checkOpArg (arg,(τ,s)) = do
        τ_arg <- checkSens arg scope
        mscale (svar s)
        unify (Numeric τ) τ_arg
  in do
    (res,arg_sens) <- makeTypeOp op (length args)
    _ <- msum ((checkOpArg <$> (zip args arg_sens)))
    return (Numeric res)

checkSens t scope = throwError (UnsupportedTermError t)




