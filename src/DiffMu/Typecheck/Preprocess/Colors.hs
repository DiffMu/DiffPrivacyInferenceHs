
{-# LANGUAGE TemplateHaskell #-}

module DiffMu.Typecheck.Preprocess.Colors where

import DiffMu.Prelude
import DiffMu.Abstract
import DiffMu.Core
import DiffMu.Core.Logging
import DiffMu.Typecheck.Preprocess.Common

import qualified Data.Text as T
import Data.Foldable

import qualified Data.HashSet as H
 
import Debug.Trace

-----------------------------------------------------------------------------------
-- preprocessing step to make Lets into Bind, 

type Color = AnnotationKind

instance Default (H.HashSet TeVar) where
    def = H.empty

data ColorFull = ColorFull
  {
    _functionNames :: H.HashSet TeVar,
    _inferredColor :: Color
  }

-- the monad keeping the state we require to generate unique names
type ColorTC = LightTC Location_PrePro_Demutation ColorFull

$(makeLenses ''ColorFull)

setColor :: (MonadState ColorFull m) => Color -> m ()
setColor color = inferredColor %%= (\c -> ((), color))

getColor :: (MonadState ColorFull m) => m (Color)
getColor = inferredColor %%= (\c -> (c, c))

-- push a function
pushFunction :: (MonadState ColorFull m) => TeVar -> m ()
pushFunction name = functionNames %%= (\set -> ((), H.insert name set))

isPFunction :: (MonadState ColorFull m) => TeVar -> m Bool
isPFunction name = functionNames %%= (\set -> (H.member name set, set))

pushFunctionArgs :: (MonadState ColorFull m) => [Asgmt JuliaType] -> m ()
pushFunctionArgs args = let pushArg (Just x :- t) = case t of
                                JTPFunction -> pushFunction x
                                _ -> pure ()
                            pushArg (Nothing :- _) = pure ()
                        in do
                            mapM pushArg args
                            pure ()

pushFunctionArgsRel :: (MonadState ColorFull m) => [Asgmt (JuliaType, Relevance)] -> m ()
pushFunctionArgsRel args = pushFunctionArgs [(x :- t) | (x :- (t,_)) <- args]

errorExpectSens = throwError . (TermColorError SensitivityK)
errorExpectPriv = throwError . (TermColorError PrivacyK)

processColors :: DMTerm -> ColorTC DMTerm
processColors term = do
    nterm <- handleAnyTerm term
    logForce $ "-----------------------------------"
    logForce $ "Color corrected term is:\n" <> showPretty nterm
    return nterm

handleSensTerm :: DMTerm -> ColorTC DMTerm
handleSensTerm term = do
    tterm <- transformLets (Just SensitivityK) term
    cterm <- getColor
    case cterm of
        PrivacyK -> errorExpectSens term
        SensitivityK -> return tterm
        
handlePrivTerm :: DMTerm -> ColorTC DMTerm
handlePrivTerm term = do
    tterm <- transformLets (Just PrivacyK) term
    cterm <- getColor
    case cterm of
        PrivacyK -> return tterm
        SensitivityK -> errorExpectPriv tterm --return (Ret tterm)

handleAnyTerm :: DMTerm -> ColorTC DMTerm
handleAnyTerm term = transformLets Nothing term

retPriv :: DMTerm -> ColorTC DMTerm
retPriv t = setColor PrivacyK >> return t

retSens :: DMTerm -> ColorTC DMTerm
retSens t = setColor SensitivityK >> return t

retRequired :: Maybe Color -> DMTerm -> ColorTC DMTerm
retRequired reqc term = case reqc of
                             Just PrivacyK -> setColor PrivacyK >> return (Ret term)
                             _ -> setColor SensitivityK >> return term

-- in a dmterm, apply all variable name substitutions contained in the hashmap recursively.
transformLets :: Maybe Color -> DMTerm -> ColorTC DMTerm
transformLets reqc term = case term of

   SLetBase PureLet (Just x :- t) body tail -> do
       logForce $ "handling slet "<>show x<>"with color "<>show reqc
       tbody <- handleAnyTerm body
       cbody <- getColor
       logForce $ "handling slet "<>show x<>" with color " <>show reqc<>" got "<>show (tbody, cbody)
       
       case cbody of
            SensitivityK -> do
                ttail <- transformLets reqc tail
                logForce $ "handling slet "<>show x<>" tail got "<>show (ttail)
                return (SLetBase PureLet (Just x :- t) tbody ttail)
            PrivacyK -> do
                ttail <- handlePrivTerm tail
                return (SLetBase BindLet (Just x :- t) tbody ttail)

   TLetBase PureLet ns body tail -> do
       tbody <- handleAnyTerm body
       cbody <- getColor
       case cbody of
            SensitivityK -> do
                ttail <- transformLets reqc tail
                return (TLetBase PureLet ns tbody ttail)
            PrivacyK -> do
                ttail <- handlePrivTerm tail
                return (TLetBase BindLet ns tbody ttail)
             
   Lam args body -> do
       pushFunctionArgs args
       tbody <- handleSensTerm body
       return (Lam args tbody)

   LamStar args body -> do
       pushFunctionArgsRel args
       tbody <- handlePrivTerm body
       retSens (LamStar args tbody) -- while the body is a priv term, the LamStar is a sens term
       
   TLetBase SampleLet ns body tail -> do
       tbody <- handleSensTerm body
       ttail <- handlePrivTerm tail
       setColor PrivacyK
       return (TLetBase SampleLet ns tbody ttail)
   
   FLet name (LamStar args body) tail -> do
       pushFunction name -- collect privacy function names, all other functions are assumed to be sens functions
       tf <- handleAnyTerm (LamStar args body)
       ttail <- handleAnyTerm tail
       return (FLet name tf ttail)

   FLet name (Lam args body) tail -> do
       tf <- handleAnyTerm (Lam args body)
       ttail <- handleAnyTerm tail
       return (FLet name tf ttail)

   Loop n cs (x1, x2) body -> do
       tn <- handleSensTerm n
       tbody  <- handleAnyTerm body
       return (Loop tn cs (x1, x2) tbody)
       
   Apply f xs -> do
       txs <- mapM handleSensTerm xs
       case f of
            Var (Just fn :- _) -> do
                                    isP <- isPFunction fn
                                    case isP of
                                       True  -> retPriv (Apply f txs)
                                       False -> retSens (Apply f txs) -- f is either a sfunc arg or not in scope
            _ -> do -- there are no functions that return priv functions, so we can assume here that this is a sens function
                   tf <- handleSensTerm f
                   retSens (Apply tf txs)
                   
   Sng _ _ -> retRequired reqc term
   Var _ -> retRequired reqc term
   Arg _ _ _ -> retRequired reqc term
   
   TLetBase _ _ _ _ -> throwError (InternalError ("Parser spit out a non-pure TLet: " <> show term))
   SLetBase _ _ _ _ -> throwError (InternalError ("Parser spit out a non-pure SLet: " <> show term))
   FLet _ _ _ -> throwError (InternalError ("Parser spit out an FLet that has no lambda in its definition: " <> show term))

   Ret _ -> throwError (InternalError ("Parser spit out a return term: " <> show term))

   _ -> case reqc of
             Just PrivacyK -> do
                                   tterm <- recDMTermMSameExtension handleAnyTerm term
                                   logForce $ "handling privacy term "<>show term<>" got " <> show (tterm)
                                   col <- getColor
                                   setColor PrivacyK
                                   case col of
                                        SensitivityK -> return (Ret tterm)
                                        PrivacyK -> return tterm
             _ -> do
                             tterm <- recDMTermMSameExtension handleSensTerm term
                             logForce $ "handling sens term "<>show term<>" as col is " <> show reqc <> " got " <> show (tterm)
                             case term of
                                 Gauss _ _ _ _ -> retPriv tterm
                                 Laplace _ _ _ -> retPriv tterm
                                 _ ->  retSens tterm

{-   
-}
