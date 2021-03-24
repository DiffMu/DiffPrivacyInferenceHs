
module DiffMu.Typecheck.Typecheck where

import DiffMu.Prelude
import DiffMu.Core
import DiffMu.Core.Symbolic
import DiffMu.Core.MonadicPolynomial
import DiffMu.Core.TC
import DiffMu.Core.MonadTC

import Data.HashMap.Strict as H

createDMType :: MonadDMTC e t => JuliaType -> t e DMType
createDMType JTInt = pure DMInt
createDMType JTReal = pure DMReal
createDMType JTAny = newType "any"

-- instance (Eq v, Hashable v) => HashKey v where

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
checkSens (Sng η τ) scope  = Const (injectCoeffId (Fin η)) <$> createDMType τ

-- a special term for function argument variables.
-- those get sensitivity 1, all other variables are var terms
checkSens (Arg x dτ) scope = do τ <- createDMType dτ
                                setVar x (τ :@ injectCoeffId (Fin 1)) --(Fin 1))
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
                                    addConstraint'2 (IsLessEqual (τ, dτd) )
                                    return τ

checkSens t scope = throwError (UnsupportedTermError t)



