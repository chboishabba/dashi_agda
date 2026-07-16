module DASHI.Physics.YangMills.BalabanCMP122ToStepV where

-- Exact consumer test for CMP 122 II, Theorem 1.
--
-- CMP 122 may plausibly discharge the current P10/P11 source slots, but the
-- present Step-V certificate also depends on separate P06 entropy and P33
-- regularity inputs.  This module keeps that separation explicit.  It is a
-- successful adapter only once `CMP122ToCurrentStepVMapping` is inhabited by
-- a theorem-by-theorem audit of Sect. 2 [III] and CMP 122 II.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([])

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.BalabanCMP122ConditionalRGClosure using
  ( BalabanCMP122ConditionalRGClosure )
open import DASHI.Physics.YangMills.BalabanStepVSpatialKPCertificate using
  ( BalabanStepVSpatialKPCertificate )
import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as ADC
import DASHI.Physics.YangMills.YMSourceAuthoritySurface as Authority

record CMP122ToCurrentStepVMapping
    (cmp122 : BalabanCMP122ConditionalRGClosure) : Set₁ where
  field
    -- These are the two existing Step-V source slots which the published
    -- R-operation theorem could discharge.  Their exact legacy types are
    -- retained so the adapter cannot hide a change of norm or carrier.
    p10LargeFieldActivity :
      ∀ k X → Assembly.LargeField.LargeFieldPolymer k X →
      Assembly.LargeField.sourceLargeFieldActivity k X
        Assembly._≤ℝ_
        Assembly.LargeField.P10CanonicalDiameterEnvelope
          Assembly.LargeField.currentP10AdmissibleConstants X

    p11AbsorptionCondition : Assembly.LargeField.ImportedAbsorptionCondition

    -- The following fields are audit assertions, not consequences of merely
    -- naming Theorem 1.  They say which literal clauses must be verified.
    identifiesActivityNorm : Set
    identifiesSummability : Set
    identifiesIncompatibilityControl : Set
    identifiesScaleVolumeUniformity : Set
    identifiesNextStepClosure : Set

    sourceAuthorityId : Authority.SourceAuthorityId
    theoremLocator : String
    status : Authority.VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open CMP122ToCurrentStepVMapping public

-- Mechanical composition only.  P06 and P33 are intentionally passed in:
-- CMP 122 Theorem 1 does not make their current DASHI witnesses definitional.
balabanCMP122ImpliesStepV :
  (cmp122 : BalabanCMP122ConditionalRGClosure) →
  CMP122ToCurrentStepVMapping cmp122 →
  Entropy.ImportedPolymerAnimalCountingBound →
  ADC.P33aUniformLinkEllipticityWrapper →
  Assembly.StepVInternalReducers →
  BalabanStepVSpatialKPCertificate
balabanCMP122ImpliesStepV cmp122 mapping p06 p33 reducers = record
  { entropyBound = Entropy.currentPolymerDiameterEntropyBound
  ; diameterCompatibility = ADC.currentAnisotropicDiameterCompatibility
  ; largeFieldSuppression = Assembly.LargeField.currentLargeFieldSuppressionBound
  ; stepVSourceAnalyticInputs = record
      { p06AnimalCounting = p06
      ; p06MixedReducerPayload =
          Entropy.ImportedPolymerAnimalCountingBound.mixedReducerPayload p06
      ; p06MixedReducerPayloadMatches = refl
      ; p10LargeFieldActivity = p10LargeFieldActivity mapping
      ; p11AbsorptionCondition = p11AbsorptionCondition mapping
      ; p33aUniformLinkEllipticity = p33
      }
  ; stepVInternalReducers = reducers
  ; assembledStepVCertificate =
      Assembly.StepVFromDischargePackages
        (record
          { p06AnimalCounting = p06
          ; p06MixedReducerPayload =
              Entropy.ImportedPolymerAnimalCountingBound.mixedReducerPayload p06
          ; p06MixedReducerPayloadMatches = refl
          ; p10LargeFieldActivity = p10LargeFieldActivity mapping
          ; p11AbsorptionCondition = p11AbsorptionCondition mapping
          ; p33aUniformLinkEllipticity = p33
          })
        reducers
  ; assembledStepVRGStructure = Assembly.currentStepVRGAssemblyBundle
  ; weightedArithmeticCloses =
      Assembly.KP76.anisotropicKPArithmeticClosedIsTrue
        Assembly.KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
  ; polymerDiameterEntropyControlled = true
  ; anisotropicDiameterLossControlled = true
  ; largeFieldSuppressionControlled = true
  ; allDiameterKPCertificate = true
  ; polymerDiameterEntropyControlledIsTrue = refl
  ; anisotropicDiameterLossControlledIsTrue = refl
  ; largeFieldSuppressionControlledIsTrue = refl
  ; allDiameterKPCertificateIsTrue = refl
  ; targetInequality =
      "CMP 122 Theorem 1 supplies the audited P10/P11 Step-V slots; P06/P33 remain explicit independent inputs."
  ; openObligations = []
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }

-- Fail-closed result of the two-module test.  The wrapper is present, but
-- the mapping awaits literal identification of Sect. 2 [III] bounds with the
-- legacy diameter-envelope and absorption-condition APIs.
currentCMP122ToCurrentStepVMappingAvailable : Set
currentCMP122ToCurrentStepVMappingAvailable = ⊥
