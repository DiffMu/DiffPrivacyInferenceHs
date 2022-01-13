
module Spec.Demutation where

import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.FLetReorder
import DiffMu.Typecheck.Preprocess.Demutation
import DiffMu.Typecheck.Preprocess.Common
import DiffMu.Typecheck.Preprocess.All
import Spec.Base


checkMutTerm :: MutDMTerm -> IO Bool
checkMutTerm term = do
  let r = do

        log $ "Checking term   : " <> show term
        -- typecheck the term t5
        -- mt <- thisFunctionDoesNotExist term

        term' <- liftNewLightTC (preprocessAll term)


        let tres = checkSens def (term')
        -- let (tres'',_) = runState (extractDelayed def tres) def
        -- tres' <- tres''
        tres' <- tres
        log $ "Type before constraint resolving: " <> show tres'
        log $ "solving constraints:"
        logPrintConstraints
        solveAllConstraints [SolveSpecial,SolveExact,SolveGlobal,SolveAssumeWorst,SolveFinal]
        tres'' <- normalize tres'
        return tres''

  -- these are the locations from which the logs will be shown
  let logging_locations = [
        Location_Check,
        Location_Constraint
        -- Location_Subst
        -- Location_INC,
        -- Location_MonadicGraph,
         --Location_All
        ]

  x <- executeTC (DoShowLog Info logging_locations) r

  case x of
    Left err -> (putStrLn $ "Encountered error: " <> show err) >> return False
    Right x -> (putStrLn $ "Result: " <> show x) >> return True


testDemutation = do
  describe "loop demutation" $ do
  --   it "example 0" $ do
  --     let v s = UserTeVar (Symbol s)
  --     let n i = (Sng i (JuliaType "Integer"))
  --     let term = FLet (Just (v "f"))
  --                (
  --                  Lam [(v "a" :- JTAny) , (Just (v "b") :- JTAny)]
  --                  (
  --                    Extra (MutLet PureLet (ConvertM (Var (Just (v "b") :- JTAny)))
  --                    (
  --                      SLet (v "a" :- JTAny) (Op (IsBinary DMOpAdd) [Var (v "a" :- JTAny) , n 1])
  --                      (
  --                        Var (v "a" :- JTAny)
  --                      )
  --                    ))
  --                  )
  --                )
  --                (Var (Just (v "f") :- JTAny))

  --     (checkMutTerm term) `shouldReturn` True

    -- it "example 0.2" $ do
    --   let v s = UserTeVar (Symbol s)
    --   let n i = (Sng i (JuliaType "Integer"))
    --   let term = FLet (Just (v "f"))
    --              (
    --                Lam [(v "a" :- JTAny) , (Just (v "b") :- JTAny)]
    --                (
    --                  Extra (MutLet PureLet (ConvertM (Var (Just (v "b") :- JTAny)))
    --                  (
    --                    (Op (IsBinary DMOpAdd) [Var (v "a" :- JTAny) , n 1])
    --                  ))
    --                )
    --              )
    --              (Var (Just (v "f") :- JTAny))

    --   (checkMutTerm term) `shouldReturn` True


    -- it "example 1" $ do
    --   let v s = UserTeVar (Symbol s)
    --   let n i = (Sng i (JuliaType "Integer"))
    --   let term = FLet (Just (v "f"))
    --              (
    --                Lam [(v "a" :- JTAny) , (Just (v "b") :- JTAny)]
    --                (
    --                  Extra (MutLoop (n 7) (v "i")
    --                        (
    --                          SLet (v "a" :- JTAny) (Op (IsBinary DMOpAdd) [Var (v "a" :- JTAny) , n 1])
    --                          (
    --                            Var (v "a" :- JTAny)
    --                          )
    --                        )
    --                        )
    --                )
    --              )
    --              (Var (Just (v "f") :- JTAny))

    --   (checkMutTerm term) `shouldReturn` True


    it "example 2 (loop)" $ do
      let v s = UserTeVar (Symbol s)
      let n i = (Sng i (JTInt))
      let term = FLet (v "f")
                 (
                   Lam [(Just (v "a") :- JTAny) , (Just (v "b") :- JTAny) , (Just (v "c") :- JTAny)]
                   (
                     Extra (MutLoop (n 7) (Just (v "i"))
                     (
                       Extra (MutLet PureLet (ConvertM (Var (Just (v "b") :- JTAny)))
                       (
                        Extra (MutLet PureLet (ConvertM (Var (Just (v "c") :- JTAny)))
                        (
                         Extra (MutLet PureLet (SLet (Just (v "a") :- JTAny) (Op (IsBinary DMOpAdd) [Var (Just (v "a") :- JTAny) , n 1])
                                        (
                                          Var (Just (v "b") :- JTAny)
                                        ))
                         (
                           Extra MutRet
                         ))
                        ))
                       ))
                     ))
                   )
                 )
                 (Var (Just (v "f") :- JTAny))

      (checkMutTerm term) `shouldReturn` True

    it "example 3 (if)" $ do
      let v s = UserTeVar (Symbol s)
      let n i = (Sng i (JTInt))
      let term = FLet (v "f")
                 (
                   Lam [(Just (v "cond") :- JTAny), (Just (v "a") :- JTAny) , (Just (v "b") :- JTAny) , (Just (v "c") :- JTAny)]
                   (
                     Phi (Var (Just (v "cond") :- JTAny))
                     -- branch 1
                     (Extra (MutLet PureLet (ConvertM (Var (Just (v "b") :- JTAny)))
                     (
                       ConvertM (Var (Just (v "a") :- JTAny))))
                     )

                     -- branch 2
                     (ConvertM (Var (Just (v "c") :- JTAny)))
                   )
                 )
                 (Var (Just (v "f") :- JTAny))

      (checkMutTerm term) `shouldReturn` True

    it "example 3.1 (if with non mutating branch)" $ do
      let v s = UserTeVar (Symbol s)
      let n i = (Sng i (JTInt))
      let term = FLet (v "f")
                 (
                   Lam [(Just (v "cond") :- JTAny), (Just (v "a") :- JTAny) , (Just (v "b") :- JTAny) , (Just (v "c") :- JTAny)]
                   (
                     Phi (Var (Just (v "cond") :- JTAny))
                     -- branch 1
                     (Extra (MutLet PureLet (ConvertM (Var (Just (v "b") :- JTAny)))
                     (
                       ConvertM (Var (Just (v "a") :- JTAny))))
                     )

                     -- branch 2
                     (SLet (Just (v "a") :- JTAny) (Op (IsBinary DMOpAdd) [Var (Just (v "a") :- JTAny) , n 1])
                     (
                       Var (Just (v "a") :- JTAny)
                     ))
                   )
                 )
                 (Var (Just (v "f") :- JTAny))

      (checkMutTerm term) `shouldReturn` True

