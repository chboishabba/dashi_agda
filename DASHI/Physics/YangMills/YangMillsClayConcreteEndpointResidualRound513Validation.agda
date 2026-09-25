{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayConcreteEndpointResidualRound513Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayConcreteEndpointResidualRound513Exact as R513
open import DASHI.Physics.YangMills.CompactLieProofLevel

sourceAnalysisCountIsSeventeen :
  R513.sourceAnalysisLeafCount ≡ 17
sourceAnalysisCountIsSeventeen = refl

sourceAttachmentCountIsEighteen :
  R513.sourceLiteralAttachmentLeafCount ≡ 18
sourceAttachmentCountIsEighteen = refl

endpointSemanticCountIsTwentyOne :
  R513.endpointSemanticLeafCount ≡ 21
endpointSemanticCountIsTwentyOne = refl

residualCountIsFiftySix :
  R513.residualLeafCount ≡ 56
residualCountIsFiftySix = refl

a3EndpointSemanticsCompiled :
  R513.a3ContinuumEndpointSemanticLeafStillResidual ≡ false
a3EndpointSemanticsCompiled = refl

t3EndpointSemanticsCompiled :
  R513.t3OpaqueEndpointSemanticsStillResidual ≡ false
t3EndpointSemanticsCompiled = refl

bGapEndpointSemanticsCompiled :
  R513.bOpaqueGapEndpointSemanticsStillResidual ≡ false
bGapEndpointSemanticsCompiled = refl

g2EndpointSemanticsCompiled :
  R513.g2OpaqueNontrivialityEndpointSemanticsStillResidual ≡ false
g2EndpointSemanticsCompiled = refl

structuralT1T4StillOpen :
  R513.structuralT1T4EndpointSemanticsStillResidual ≡ true
structuralT1T4StillOpen = refl

residualCompilerMachineChecked :
  R513.round513ConcreteEndpointResidualCompilerLevel ≡ machineChecked
residualCompilerMachineChecked = refl
