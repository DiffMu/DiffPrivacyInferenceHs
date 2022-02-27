
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
-- preprocessing step to make Lets into Bind (and add Ret if necessary)
-- infers the color (whether its a priv or a sens term) recursively and, upon
-- encountering SLet/TLet, makes them into Bind if they are supposed to be.
-- they are supposed to be if the term that is assigned is a privacy term.
-- it is then required for the tial term to be a privacy term too, which is why
-- the main function takes the required color as input. it inserts Ret if the term
-- cannot be interpreted as a privacy term otherwise.

------------------------------------------------
-- the state for our computation:
--    functionNames = the list of privacy functions in scope
--    inferredColor = the color that was inferred
type Color = AnnotationKind

instance Default (H.HashSet TeVar) where
    def = H.empty

data ColorFull = ColorFull
  {
    _functionNames :: H.HashSet TeVar,
    _inferredColor :: Color
  }

type ColorTC = LightTC Location_PrePro_Color ColorFull

$(makeLenses ''ColorFull)

-- set current inferred color
setColor :: (MonadState ColorFull m) => Color -> m ()
setColor color = inferredColor .= color

-- get current inferred color
getColor :: (MonadState ColorFull m) => m (Color)
getColor = use inferredColor

-- push a function name to the privacy function scope
pushFunction :: (MonadState ColorFull m) => TeVar -> m ()
pushFunction name = functionNames %%= (\set -> ((), H.insert name set))

-- check if a name corresponds t a privacy function
isPFunction :: (MonadState ColorFull m) => TeVar -> m Bool
isPFunction name = functionNames %%= (\set -> (H.member name set, set))

-- push all names to the priv function scope that are annotated as privacy
-- functions in the given argument list.
pushFunctionArgs :: (MonadState ColorFull m) => [Asgmt JuliaType] -> m ()
pushFunctionArgs args = let pushArg (x :- t) = case t of
                                JTPFunction -> pushFunction x -- user annotation says its a priva function
                                _ -> pure ()
                        in do
                            mapM pushArg args
                            pure ()

-- same as above but for argument lists that have relevance annotations too
pushFunctionArgsRel :: (MonadState ColorFull m) => [Asgmt (JuliaType, Relevance)] -> m ()
pushFunctionArgsRel args = pushFunctionArgs [(x :- t) | (x :- (t,_)) <- args]


------------------------------------------------

-- the function to be called from the outside, just for the log print
processColors :: DMTerm -> ColorTC DMTerm
processColors term = do
    nterm <- handleAnyTerm term
    logForce $ "-----------------------------------"
    logForce $ "Color corrected term is:\n" <> showPretty nterm
    return nterm

-- handle a term that is required to be a sensitivity term
handleSensTerm :: DMTerm -> ColorTC DMTerm
handleSensTerm term = do
    tterm <- transformLets (Just SensitivityK) term
    cterm <- getColor
    case cterm of
        PrivacyK -> throwError (TermColorError SensitivityK term)
        SensitivityK -> return tterm
        
-- handle a term that is required to be a privacy term
handlePrivTerm :: DMTerm -> ColorTC DMTerm
handlePrivTerm term = do
    tterm <- transformLets (Just PrivacyK) term
    cterm <- getColor
    case cterm of
        PrivacyK -> return tterm
        SensitivityK -> throwError (TermColorError PrivacyK tterm)

-- handle a term that can be whatever
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

-- main function. takes a requested color (or nothing if we don;t care), and the term to
-- transform. does three interesting things:
--    Lets are turned into Binds if the thing that is assigned is inferred to be a privacy term.
--    If so, the trailing term is requested to be a privacy term. If not, the trailing term is
--    requested to be the requested color.
--
--    All privacy functions that occur are collected in a name context. Upon application their
--    presence in the context is checked to determine the return color.
--
--    Sensitivity terms are prepended by a Ret if they are requested to be privacy terms.
transformLets :: Maybe Color -> DMTerm -> ColorTC DMTerm
transformLets reqc term = case term of

   SLetBase PureLet (x :- t) body tail -> do
       tbody <- handleAnyTerm body
       cbody <- getColor
       case cbody of
            SensitivityK -> do
                ttail <- transformLets reqc tail
                return (SLetBase PureLet (x :- t) tbody ttail)
            PrivacyK -> do
                ttail <- handlePrivTerm tail
                return (SLetBase BindLet (x :- t) tbody ttail)

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
             
   Reorder σ t -> do
       tt <- handleAnyTerm t
       return (Reorder σ tt)

   Lam args body -> do
       pushFunctionArgs args
       tbody <- handleSensTerm body
       return (Lam args tbody)

   LamStar args body -> do
       pushFunctionArgsRel args
       fn <- use functionNames
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
            Var (fn :- _) -> do
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
                                   case term of
                                       Gauss _ _ _ _ -> retPriv tterm
                                       Laplace _ _ _ -> retPriv tterm
                                       AboveThresh _ _ _ _ -> retPriv tterm
                                       Exponential _ _ _ _ -> retPriv tterm
                                       _ ->  retPriv (Ret tterm)
             _ -> do
                             tterm <- recDMTermMSameExtension handleSensTerm term
                             case term of
                                 Gauss _ _ _ _ -> retPriv tterm
                                 Laplace _ _ _ -> retPriv tterm
                                 AboveThresh _ _ _ _ -> retPriv tterm
                                 Exponential _ _ _ _ -> retPriv tterm
                                 _ ->  retSens tterm

