
module DiffMu.Core.Subtyping where

import DiffMu.Prelude
import DiffMu.Core.Definitions
import DiffMu.Core.MonadTC
import DiffMu.Core.Context
import DiffMu.Core.TC
import DiffMu.Core.Term
import DiffMu.Core.MonadicPolynomial2
import DiffMu.Core.Symbolic
import DiffMu.Core.Unification
import DiffMu.Core.INC
import DiffMu.Core.MonadicGraph

import Debug.Trace

(⊑!) :: (SingI k, Typeable k, MonadDMTC e t) => DMTypeOf k -> DMTypeOf k -> t e ()
(⊑!) a b = addConstraint (Solvable (IsLessEqual (a,b))) >> pure ()

getArrowLength :: DMType -> Maybe Int
getArrowLength (a :->: _) = Just (length a)
getArrowLength _         = Nothing

subtypingGraph :: forall e t k. (SingI k, Typeable k, MonadDMTC e t) => EdgeType -> [Edge (t e) (DMTypeOf k)]
subtypingGraph =
  let case1 = testEquality (typeRep @k) (typeRep @MainKind)
      case2 = testEquality (typeRep @k) (typeRep @NumKind)
      case3 = testEquality (typeRep @k) (typeRep @BaseNumKind)
  in case (case1,case2,case3) of
    -- Main Kind
    (Just Refl, _, _) ->
      \case { IsReflexive IsStructural
              -> [ MultiEdge getArrowLength $
                   \n -> do
                     let f () = do a <- newVar
                                   b <- newVar
                                   b ⊑! a
                                   s <- newVar
                                   return (a :@ s, b :@ s)

                     args <- mapM f (take n $ repeat ())
                     let (args₀, args₁) = unzip args
                     r₀ <- newVar
                     r₁ <- newVar
                     r₀ ⊑! r₁
                     return (args₀ :->: r₀, args₁ :->: r₁)

                 , SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return (Numeric a₀, Numeric a₁)
                 ]
            ; IsReflexive NotStructural -> []
            ; NotReflexive -> []
            }

    -- Num Kind
    (_, Just Refl, _) ->
      \case { IsReflexive IsStructural
              -> []
            ; IsReflexive NotStructural
              -> [ SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      return (NonConst a₀, NonConst a₁)
                 , SingleEdge $
                   do a₀ <- newVar
                      a₁ <- newVar
                      a₀ ⊑! a₁
                      s₀ <- newVar
                      return (Const s₀ a₀, Const s₀ a₁)
                 ]
            ; NotReflexive
              -> [ SingleEdge $
                   do a₀ <- newVar
                      s₀ <- newVar
                      return (Const s₀ a₀, NonConst a₀)
                 ]
            }

    -- BaseNum Kind
    (_, _, Just Refl) ->
      \case { IsReflexive NotStructural
              -> [ SingleEdge $ return (DMInt, DMInt)
                 , SingleEdge $ return (DMReal, DMReal)
                 ]
            ; IsReflexive IsStructural
              -> []
            ; NotReflexive
              -> [ SingleEdge $ return (DMInt, DMReal)
                 ]
            }
    (_, _, _) -> \_ -> []

-- subtypingGraph :: forall e t k. (SingI k, Typeable k, MonadDMTC e t) => NodeType -> [t e (DMTypeOf k,DMTypeOf k)]
-- subtypingGraph = case testEquality (typeRep @k) (typeRep @MainKind) of
--   Just Refl -> \case { IsReflexive IsStructural  -> [ do a <- TVar <$> newTVar "a"
--                                                          s <- svar <$> newSVar "s"
--                                                          b <- TVar <$> newTVar "b"
--                                                          return ([a :@ s] :->: b, [a :@ s] :->: b)
--                                                     ]
--                      ; IsReflexive NotStructural -> []
--                      ; NotReflexive -> []
--                      }
--   Nothing -> case testEquality (typeRep @k) (typeRep @BaseNumKind) of
--     Just Refl -> \case { IsReflexive NotStructural -> [ return (DMInt, DMInt), return (DMReal, DMReal)]
--                        ; IsReflexive IsStructural  -> []
--                        ; NotReflexive -> [ return (DMInt, DMReal)]
--                        }
--     Nothing -> \case {_ -> []}


solveSubtyping :: forall t e k. (SingI k, Typeable k, IsT MonadDMTC t) => Symbol -> (DMTypeOf k, DMTypeOf k) -> t e ()
solveSubtyping name path = do
  let relevance e = IsGraphRelevant
  traceM $ "Starting subtyping solving of " <> show path
  let graph = subtypingGraph @e @t
  traceM $ "I have " <> show (length (graph (IsReflexive NotStructural))) <> " candidates."

  res <- findPathM @(Full e) @_ @DMException relevance (GraphM graph) path
  case res of
    Finished a -> traceM ("subtyping finished with: " <> show a) >> dischargeConstraint @MonadDMTC name
    Partial a -> updateConstraint name (Solvable (IsLessEqual a))
    Wait -> return ()
    Fail e -> throwError (UnsatisfiableConstraint (show (fst path) <> " ⊑ " <> show (snd path) <> "\n\n"
                         <> "Got the following errors while search the subtyping graph:\n"
                         <> show e))


instance (SingI k, Typeable k) => Solve MonadDMTC IsLessEqual (DMTypeOf k, DMTypeOf k) where
  -- solve_ (IsLessEqual (a,b)) = undefined
  solve_ Dict _ name (IsLessEqual (a,b)) = solveSubtyping name (a,b)



instance Solve MonadDMTC IsSupremum (DMTypeOf k, DMTypeOf k, DMTypeOf k) where
  solve_ Dict _ _ a = pure () -- undefined







