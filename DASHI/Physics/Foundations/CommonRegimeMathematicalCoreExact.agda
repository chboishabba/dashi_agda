{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CommonRegimeMathematicalCoreExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Shared

------------------------------------------------------------------------
-- COMMON OVERLAP/BACKREACTION MATHEMATICS WITHOUT REGIME PROMOTION TOKEN
------------------------------------------------------------------------

record CommonRegimeMathematicalCore (U : Weld.UnifiedCandidate) : Set₁ where
  field
    overlapRegime :
      Weld.Regime U

    overlapIsGR :
      Weld.grRegime U overlapRegime

    overlapIsQFT :
      Weld.qftRegime U overlapRegime

    backreactionConsistency :
      ∀ candidate →
      Weld.BackreactionConsistent U
        (Weld.coarseGrain U candidate overlapRegime)
        overlapRegime

    correctionControl :
      ∀ candidate →
      Weld.CorrectionsControlled U
        (Weld.coarseGrain U candidate overlapRegime)
        overlapRegime

open CommonRegimeMathematicalCore public

attachRegimePromotionToken :
  ∀ {U : Weld.UnifiedCandidate} →
  CommonRegimeMathematicalCore U →
  Weld.RegimeRecoveryToken U →
  Weld.CommonRegimeRecovery U
attachRegimePromotionToken core token = record
  { Weld.CommonRegimeRecovery.overlapRegime =
      overlapRegime core
  ; Weld.CommonRegimeRecovery.overlapIsGR =
      overlapIsGR core
  ; Weld.CommonRegimeRecovery.overlapIsQFT =
      overlapIsQFT core
  ; Weld.CommonRegimeRecovery.backreactionConsistency =
      backreactionConsistency core
  ; Weld.CommonRegimeRecovery.correctionControl =
      correctionControl core
  ; Weld.CommonRegimeRecovery.regimePromotionToken =
      token
  }

sharedSourceControlToMathematicalCore :
  ∀ {U : Weld.UnifiedCandidate}
    {source : Shared.SharedEffectiveSourceTheory U} →
  Shared.SharedSourceRegimeControl source →
  CommonRegimeMathematicalCore U
sharedSourceControlToMathematicalCore control = record
  { CommonRegimeMathematicalCore.overlapRegime =
      Shared.overlapRegime control
  ; CommonRegimeMathematicalCore.overlapIsGR =
      Shared.overlapIsGR control
  ; CommonRegimeMathematicalCore.overlapIsQFT =
      Shared.overlapIsQFT control
  ; CommonRegimeMathematicalCore.backreactionConsistency =
      Shared.backreactionFromSharedSource control
  ; CommonRegimeMathematicalCore.correctionControl =
      Shared.correctionsControlledOnSharedSource control
  }

regimePromotionTokenIsMathematicalOverlapPremise : Bool
regimePromotionTokenIsMathematicalOverlapPremise = false

regimePromotionTokenIsMathematicalOverlapPremiseIsFalse :
  regimePromotionTokenIsMathematicalOverlapPremise ≡ false
regimePromotionTokenIsMathematicalOverlapPremiseIsFalse = refl

commonOverlapBackreactionCorrectionsStillMathematical : Bool
commonOverlapBackreactionCorrectionsStillMathematical = true

commonOverlapBackreactionCorrectionsStillMathematicalIsTrue :
  commonOverlapBackreactionCorrectionsStillMathematical ≡ true
commonOverlapBackreactionCorrectionsStillMathematicalIsTrue = refl
