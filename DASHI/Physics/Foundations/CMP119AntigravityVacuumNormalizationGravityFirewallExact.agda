{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum

------------------------------------------------------------------------
-- VACUUM NORMALIZATION != GRAVITATIONAL VACUUM STRESS
--
-- Recovering the CMP119 normalization/vacuum coordinate does not numerically
-- identify it with a physical cosmological amplitude.  Physical promotion is a
-- same-state theorem about the metric/volume response of the RENORMALIZED
-- effective action plus a cosmological renormalization convention and the
-- required normalization/unit calibration.
------------------------------------------------------------------------

record VacuumNormalizationToGravityReceipt
    (sourceNormalization : ℚ) : Set₁ where
  field
    renormalizedGravitationalAmplitude : ℚ
    physicalVacuumStress : Stress.RationalTensor4

    NormalizationToGravitySameObjectReceipt : Set
    normalizationToGravitySameObjectReceipt :
      NormalizationToGravitySameObjectReceipt

    -- The selected renormalized effective action really has the vacuum metric
    -- variation on the physical state/metric carrier.
    renormalizedEffectiveActionMetricResponse :
      ∀ a b →
      physicalVacuumStress a b
      ≡ renormalizedGravitationalAmplitude * Vacuum.negativeMetric a b

    CosmologicalRenormalizationCondition : Set
    cosmologicalRenormalizationCondition :
      CosmologicalRenormalizationCondition

    SameStateMetricVolumeReceipt : Set
    sameStateMetricVolumeReceipt : SameStateMetricVolumeReceipt

open VacuumNormalizationToGravityReceipt public

receiptPhysicalStressHasVacuumShape :
  ∀ {sourceNormalization}
    (receipt : VacuumNormalizationToGravityReceipt sourceNormalization)
    a b →
  physicalVacuumStress receipt a b
  ≡ renormalizedGravitationalAmplitude receipt * Vacuum.negativeMetric a b
receiptPhysicalStressHasVacuumShape receipt =
  renormalizedEffectiveActionMetricResponse receipt

record VacuumNormalizationGravityBoundary : Set where
  constructor vacuum-normalization-gravity-boundary
  field
    normalizationConstantAloneDeterminesGravitationalStress : Bool
    sourceVacuumReadoutAloneDeterminesPhysicalLambda : Bool
    sourceNormalizationNumericallyEqualsPhysicalLambdaByDefinition : Bool
    algebraicVacuumStressRayAlreadyOwned : Bool
    renormalizedEffectiveActionMetricResponseRequired : Bool
    gravitationalCosmologicalRenormalizationConditionRequired : Bool
    sameStateMetricVolumeReceiptRequired : Bool
    normalizationToGravityCalibrationStillRequired : Bool
    differentialCommonCountertermCancellationStillValid : Bool
    absoluteNormalizationCanBeShiftedBeforeGravityConvention : Bool

canonicalVacuumNormalizationGravityBoundary :
  VacuumNormalizationGravityBoundary
canonicalVacuumNormalizationGravityBoundary =
  vacuum-normalization-gravity-boundary
    false false false true true true true true true true

normalizationConstantAloneDeterminesGravitationalStress : Bool
normalizationConstantAloneDeterminesGravitationalStress = false

sourceVacuumReadoutAloneDeterminesPhysicalLambda : Bool
sourceVacuumReadoutAloneDeterminesPhysicalLambda = false

sourceNormalizationNumericallyEqualsPhysicalLambdaByDefinition : Bool
sourceNormalizationNumericallyEqualsPhysicalLambdaByDefinition = false

renormalizedEffectiveActionMetricResponseRequired : Bool
renormalizedEffectiveActionMetricResponseRequired = true

gravitationalCosmologicalRenormalizationConditionRequired : Bool
gravitationalCosmologicalRenormalizationConditionRequired = true

normalizationToGravityCalibrationStillRequired : Bool
normalizationToGravityCalibrationStillRequired = true

differentialCommonCountertermCancellationStillValid : Bool
differentialCommonCountertermCancellationStillValid = true
