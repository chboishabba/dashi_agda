{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Semantics

finiteRGProbabilitySemanticsIsCompilerOwned :
  Semantics.finiteRGProbabilitySemanticsLevel ≡ machineChecked
finiteRGProbabilitySemanticsIsCompilerOwned = refl

finiteMarkovSublevelIsCompilerOwned :
  Semantics.finiteMarkovSublevelLevel ≡ machineChecked
finiteMarkovSublevelIsCompilerOwned = refl

selectedT5ExpectationIntegralTransportIsCompilerOwned :
  Semantics.selectedT5ExpectationIntegralTransportLevel ≡ machineChecked
selectedT5ExpectationIntegralTransportIsCompilerOwned = refl

selectedWeightsStillNeedProbabilityProof :
  Semantics.selectedFiniteRGProbabilityLawLevel ≡ conditional
selectedWeightsStillNeedProbabilityProof = refl

round283PresentationStillNeedsSameObjectProof :
  Semantics.round283SelectedFinitePresentationLevel ≡ conditional
round283PresentationStillNeedsSameObjectProof = refl
