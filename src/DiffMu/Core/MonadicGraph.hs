
module DiffMu.Core.MonadicGraph where

import DiffMu.Prelude
import DiffMu.Core.INC


-- Since our nodes/edges live in a monad, the source/target of an edge need not necessarily be *really* equal, for the edge to having to be considered as reflexive.
-- Thus we add this as annotation.
data NodeType = IsReflexive | NotReflexive

newtype GraphM m a = GraphM (NodeType -> [m (a,a)])

data ErrorRelevance = IsGraphRelevant | NotGraphRelevant

findPathM :: forall s m e a. (Show e, Show a, MonadError e m, MonadState s m, MonoidM m a, CheckNeutral m a) => (e -> ErrorRelevance) -> GraphM m a -> (a,a) -> m (INCRes e (a,a))
findPathM relevance (GraphM g) path =
  let f0 :: (forall b. b -> INCRes e b) -> m (a,a) -> (a,a) -> m (INCRes e (a,a))
      f0 constr node (start,goal) = do
         (n₀, n₁) <- node
         isneutral <- checkNeutral n₀
         case isneutral of
           True  -> return Wait
           False -> do n₀'' <- start ⋆ n₀
                       n₁'' <- n₁ ⋆ goal -- we only check this in the refl case
                       return (constr (n₀'', n₁))

      f1 :: (forall b. b -> INCRes e b) -> m (a,a) -> (a,a) -> m (INCRes e (a,a))
      f1 constr node (start,goal) = do
         (n₀, n₁) <- node
         isneutral <- checkNeutral n₀
         case isneutral of
           True  -> return Wait
           False -> do n₀'' <- start ⋆ n₀
                       return (constr (n₁, goal))

      catchRelevant :: forall a b. (a -> m (INCRes e a)) -> (a -> m (INCRes e a))
      catchRelevant f a =
        catchError (f a) $ \e -> case relevance e of
                                   IsGraphRelevant -> return (Fail (UserError e))
                                   NotGraphRelevant -> throwError e

      leftRefl = [catchRelevant (f0 Finished a) | a <- g IsReflexive]
      leftCont = [catchRelevant (f1 Partial a)  | a <- g NotReflexive]

  in evalINC (INC (leftRefl <> leftCont)) path




