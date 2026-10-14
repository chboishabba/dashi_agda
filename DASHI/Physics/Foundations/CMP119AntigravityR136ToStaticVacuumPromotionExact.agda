{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityR136ToStaticVacuumPromotionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _+_; _*_)

import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Lorentz
import DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact as Static
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as VacuumRay

------------------------------------------------------------------------
-- R136 / LOCAL-C VACUUM READOUT -> STATIC VACUUM PROMOTION
--
-- The continuum/Local-C route may already have paid the hard same-state
-- Euclidean->Lorentzian stress continuation and vacuum equation-of-state work.
-- In that case the static geometry consumer should not ask for an independent
-- metric-response theorem again.
--
-- The remaining physical calibration is affine:
--
--   rho_vac = a * V_source + c.
--
-- This owner consumes a SAME-STATE R136/Local-C vacuum readout plus that affine
-- calibration and compiles the existing static
-- VacuumNormalizationToGravityReceipt.  It does not infer a or c from the
-- normalization coordinate and does not manufacture the R136/Local-C
-- same-state receipt.
------------------------------------------------------------------------

record R136StaticVacuumPromotionInput
    (sourceNormalization : ℚ) : Set₁ where
  field
    lorentzianVacuum : Lorentz.VacuumLikeLorentzianStress

    normalizationToGravityScale : ℚ
    additiveGravityRenormalization : ℚ

    vacuumRhoUsesAffineCalibration :
      Lorentz.rho (Lorentz.stress lorentzianVacuum)
      ≡ normalizationToGravityScale * sourceNormalization
        + additiveGravityRenormalization

    R136LocalCSameStateMetricResponseReceipt : Set
    r136LocalCSameStateMetricResponseReceipt :
      R136LocalCSameStateMetricResponseReceipt

    CosmologicalRenormalizationCondition : Set
    cosmologicalRenormalizationCondition :
      CosmologicalRenormalizationCondition

open R136StaticVacuumPromotionInput public

r136VacuumAmplitude :
  ∀ {sourceNormalization} →
  R136StaticVacuumPromotionInput sourceNormalization → ℚ
r136VacuumAmplitude input =
  Lorentz.rho (Lorentz.stress (lorentzianVacuum input))

compileR136VacuumToStaticReceipt :
  ∀ {sourceNormalization} →
  R136StaticVacuumPromotionInput sourceNormalization →
  Static.VacuumNormalizationToGravityReceipt sourceNormalization
compileR136VacuumToStaticReceipt input = record
  { Static.VacuumNormalizationToGravityReceipt.renormalizedGravitationalAmplitude =
      r136VacuumAmplitude input
  ; Static.VacuumNormalizationToGravityReceipt.physicalVacuumStress =
      VacuumRay.vacuumStressAt (r136VacuumAmplitude input)
  ; Static.VacuumNormalizationToGravityReceipt.NormalizationToGravitySameObjectReceipt =
      R136LocalCSameStateMetricResponseReceipt input
  ; Static.VacuumNormalizationToGravityReceipt.normalizationToGravitySameObjectReceipt =
      r136LocalCSameStateMetricResponseReceipt input
  ; Static.VacuumNormalizationToGravityReceipt.renormalizedEffectiveActionMetricResponse =
      VacuumRay.vacuumStressIsMinusLambdaMetric (r136VacuumAmplitude input)
  ; Static.VacuumNormalizationToGravityReceipt.CosmologicalRenormalizationCondition =
      CosmologicalRenormalizationCondition input
  ; Static.VacuumNormalizationToGravityReceipt.cosmologicalRenormalizationCondition =
      cosmologicalRenormalizationCondition input
  ; Static.VacuumNormalizationToGravityReceipt.SameStateMetricVolumeReceipt =
      R136LocalCSameStateMetricResponseReceipt input
  ; Static.VacuumNormalizationToGravityReceipt.sameStateMetricVolumeReceipt =
      r136LocalCSameStateMetricResponseReceipt input
  }

compiledStaticAmplitudeUsesAffineCalibration :
  ∀ {sourceNormalization}
    (input : R136StaticVacuumPromotionInput sourceNormalization) →
  Static.renormalizedGravitationalAmplitude
    (compileR136VacuumToStaticReceipt input)
  ≡ normalizationToGravityScale input * sourceNormalization
    + additiveGravityRenormalization input
compiledStaticAmplitudeUsesAffineCalibration input =
  vacuumRhoUsesAffineCalibration input

r136CanProduceStaticReceiptAfterAffineCalibration : Bool
r136CanProduceStaticReceiptAfterAffineCalibration = true

independentStaticMetricResponseReceiptRequiredAfterR136Promotion : Bool
independentStaticMetricResponseReceiptRequiredAfterR136Promotion = false

affineNormalizationToGravityCalibrationStillRequired : Bool
affineNormalizationToGravityCalibrationStillRequired = true

r136SameStateLorentzianStressStillRequired : Bool
r136SameStateLorentzianStressStillRequired = true
