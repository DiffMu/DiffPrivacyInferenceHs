
module Spec.Demutation.AliasedVectorIndexing where

import Spec.Base
import DiffMu.Core.Definitions


testScoping_AliasedVectorIndexing pp = do
  describe "Values acquired by vector indexing cannot be mutated" $ do
    testAVI01 pp

testAVI01 pp = do
  let exa = " function test()        \n\
            \   function f!(a)       \n\
            \     x = a[1,1]         \n\
            \     norm_convert!(x)   \n\
            \     x                  \n\
            \   end                  \n\
            \ end                    "


  let exb = " function test()        \n\
            \   function f!(a)       \n\
            \     x = a[1]           \n\
            \     norm_convert!(x)   \n\
            \     x                  \n\
            \   end                  \n\
            \ end                    "


  let exc = " function test()        \n\
            \   function f!(a)       \n\
            \     x = a[1,:]         \n\
            \     norm_convert!(x)   \n\
            \     x                  \n\
            \   end                  \n\
            \ end                    "

  parseEvalFail pp "01a errors (Index)" exa (DemutationError "")
  parseEvalFail pp "01b errors (VIndex)" exb (DemutationError "")
  parseEvalFail pp "01c errors (Row)" exc (DemutationError "")

