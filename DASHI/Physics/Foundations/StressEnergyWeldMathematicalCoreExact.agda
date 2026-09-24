{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.StressEnergyWeldMathematicalCoreExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld

------------------------------------------------------------------------
-- MATHEMATICAL CORE OF THE STRESS WELD
--
-- SameStressEnergyWeld contains two theorem-bearing fields and one promotion
-- token.  Separate them so the mathematical max-cut is not inflated by
-- governance/authority payload.
------------------------------------------------------------------------

record StressEnergyWeldMathematicalCore
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    qftStressAggregation : ∀ candidate →
      Weld.QFTStressAggregation U candidate
        (Weld.actualQFTSectorStressShared U candidate)
        (Weld.qftTotalStressShared U candidate)

    sameStressEnergyOnOverlap :
      ∀ candidate regime →
      Weld.grRegime U regime →
      Weld.qftRegime U regime →
      Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
        (Weld.actualGRStressEnergy U (Weld.coarseGrain U candidate regime))
      ≡
      Weld.qftTotalStressShared U (Weld.coarseGrain U candidate regime)

open StressEnergyWeldMathematicalCore public

attachStressWeldPromotionToken :
  ∀ {U : Weld.UnifiedCandidate} →
  StressEnergyWeldMathematicalCore U →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
attachStressWeldPromotionToken core token = record
  { Weld.SameStressEnergyWeld.qftStressAggregation =
      qftStressAggregation core
  ; Weld.SameStressEnergyWeld.sameStressEnergyOnOverlap =
      sameStressEnergyOnOverlap core
  ; Weld.SameStressEnergyWeld.stressWeldPromotionToken =
      token
  }

stripStressWeldPromotionToken :
  ∀ {U : Weld.UnifiedCandidate} →
  Weld.SameStressEnergyWeld U →
  StressEnergyWeldMathematicalCore U
stripStressWeldPromotionToken weld = record
  { StressEnergyWeldMathematicalCore.qftStressAggregation =
      Weld.qftStressAggregation weld
  ; StressEnergyWeldMathematicalCore.sameStressEnergyOnOverlap =
      Weld.sameStressEnergyOnOverlap weld
  }

stressWeldPromotionTokenIsMathematicalEqualityPremise : Bool
stressWeldPromotionTokenIsMathematicalEqualityPremise = false

stressWeldPromotionTokenIsMathematicalEqualityPremiseIsFalse :
  stressWeldPromotionTokenIsMathematicalEqualityPremise ≡ false
stressWeldPromotionTokenIsMathematicalEqualityPremiseIsFalse = refl

mathematicalCorePlusTokenRecoversPromotedWeld : Bool
mathematicalCorePlusTokenRecoversPromotedWeld = true

mathematicalCorePlusTokenRecoversPromotedWeldIsTrue :
  mathematicalCorePlusTokenRecoversPromotedWeld ≡ true
mathematicalCorePlusTokenRecoversPromotedWeldIsTrue = refl
