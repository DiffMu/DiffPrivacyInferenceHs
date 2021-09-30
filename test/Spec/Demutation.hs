
module Spec.Demutation where

import DiffMu.Typecheck.Mutated
import DiffMu.Typecheck.Preprocess
import Spec.Base


checkMutTerm :: MutDMTerm -> IO Bool
checkMutTerm term = do
  let r = do

        log $ "Checking term   : " <> show term
        -- typecheck the term t5
        -- mt <- thisFunctionDoesNotExist term

        term'' <- liftNewMTC (demutate term)

        term' <- preprocessDMTerm term''


        let tres = checkSens (term') def
        let (tres'',_) = runState (extractDelayed def tres) def
        tres' <- tres''
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
  --     let term = FLet (v "f")
  --                (
  --                  Lam [(v "a" :- JTAny) , (v "b" :- JTAny)]
  --                  (
  --                    Extra (MutLet (ConvertM (Var (v "b" :- JTAny)))
  --                    (
  --                      SLet (v "a" :- JTAny) (Op (IsBinary DMOpAdd) [Var (v "a" :- JTAny) , n 1])
  --                      (
  --                        Var (v "a" :- JTAny)
  --                      )
  --                    ))
  --                  )
  --                )
  --                (Var (v "f" :- JTAny))

  --     (checkMutTerm term) `shouldReturn` True

    -- it "example 0.2" $ do
    --   let v s = UserTeVar (Symbol s)
    --   let n i = (Sng i (JuliaType "Integer"))
    --   let term = FLet (v "f")
    --              (
    --                Lam [(v "a" :- JTAny) , (v "b" :- JTAny)]
    --                (
    --                  Extra (MutLet (ConvertM (Var (v "b" :- JTAny)))
    --                  (
    --                    (Op (IsBinary DMOpAdd) [Var (v "a" :- JTAny) , n 1])
    --                  ))
    --                )
    --              )
    --              (Var (v "f" :- JTAny))

    --   (checkMutTerm term) `shouldReturn` True


    -- it "example 1" $ do
    --   let v s = UserTeVar (Symbol s)
    --   let n i = (Sng i (JuliaType "Integer"))
    --   let term = FLet (v "f")
    --              (
    --                Lam [(v "a" :- JTAny) , (v "b" :- JTAny)]
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
    --              (Var (v "f" :- JTAny))

    --   (checkMutTerm term) `shouldReturn` True


    it "example 2 (loop)" $ do
      let v s = UserTeVar (Symbol s)
      let n i = (Sng i (JuliaType "Integer"))
      let term = FLet (v "f")
                 (
                   Lam [(v "a" :- JTAny) , (v "b" :- JTAny) , (v "c" :- JTAny)]
                   (
                     Extra (MutLoop (n 7) (v "i")
                     (
                       Extra (MutLet (ConvertM (Var (v "b" :- JTAny)))
                       (
                        Extra (MutLet (ConvertM (Var (v "c" :- JTAny)))
                        (
                         Extra (MutLet (SLet (v "a" :- JTAny) (Op (IsBinary DMOpAdd) [Var (v "a" :- JTAny) , n 1])
                                        (
                                          Var (v "b" :- JTAny)
                                        ))
                         (
                           Extra MutRet
                         ))
                        ))
                       ))
                     ))
                   )
                 )
                 (Var (v "f" :- JTAny))

      (checkMutTerm term) `shouldReturn` True

    it "example 3 (if)" $ do
      let v s = UserTeVar (Symbol s)
      let n i = (Sng i (JuliaType "Integer"))
      let term = FLet (v "f")
                 (
                   Lam [(v "cond" :- JTAny), (v "a" :- JTAny) , (v "b" :- JTAny) , (v "c" :- JTAny)]
                   (
                     Phi (Var (v "cond" :- JTAny))
                     -- branch 1
                     (Extra (MutLet (ConvertM (Var (v "b" :- JTAny)))
                     (
                       ConvertM (Var (v "a" :- JTAny))))
                     )

                     -- branch 2
                     (ConvertM (Var (v "c" :- JTAny)))
                   )
                 )
                 (Var (v "f" :- JTAny))

      (checkMutTerm term) `shouldReturn` True

    it "example 3.1 (if with non mutating branch)" $ do
      let v s = UserTeVar (Symbol s)
      let n i = (Sng i (JuliaType "Integer"))
      let term = FLet (v "f")
                 (
                   Lam [(v "cond" :- JTAny), (v "a" :- JTAny) , (v "b" :- JTAny) , (v "c" :- JTAny)]
                   (
                     Phi (Var (v "cond" :- JTAny))
                     -- branch 1
                     (Extra (MutLet (ConvertM (Var (v "b" :- JTAny)))
                     (
                       ConvertM (Var (v "a" :- JTAny))))
                     )

                     -- branch 2
                     (SLet (v "a" :- JTAny) (Op (IsBinary DMOpAdd) [Var (v "a" :- JTAny) , n 1])
                     (
                       Var (v "a" :- JTAny)
                     ))
                   )
                 )
                 (Var (v "f" :- JTAny))

      (checkMutTerm term) `shouldReturn` True




