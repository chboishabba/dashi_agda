{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumNormalizationGravityFirewallExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _*_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum

------------------------------------------------------------------------
-- VACUUM NORMALIZATION != GRAVITATIONAL VACUUM STRESS
--
-- Even after the CMP119 vacuum/normalization coordinate has been reconstructed
-- from the complete normalized RG density, that scalar is not automatically a
-- physical cosmological source.  Gravity couples to the metric/volume response
-- of the RENORMALIZED effective action.  An additive normalization constant can
-- be shifted by a renormalization convention until a gravitational convention
-- fixes which same-state amplitude is carried into T_{mu nu} / Lambda.
--
-- This module therefore keeps the algebraic vacuum-stress ray from
-- GRQFTVacuumStressLambdaCompilerExact, but makes the physical promotion an
-- explicit same-object receipt.
------------------------------------------------------------------------

record VacuumNormalizationToGravityReceipt
    (sourceNormalization : ℚ) : Set₁ where
  field
    renormalizedGravitationalAmplitude : ℚ
    physicalVacuumStress : Stress.RationalTensor4

    -- Same-state/source identification, not a numerical coincidence.
    sourceNormalizationSameObjectAsRenormalizedAmplitude :
      sourceNormalization ≡ renormalizedGravitationalAmplitude

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
    algebraicVacuumStressRayAlreadyOwned : Bool
    renormalizedEffectiveActionMetricResponseRequired : Bool
    gravitationalCosmologicalRenormalizationConditionRequired : Bool
    sameStateMetricVolumeReceiptRequired : Bool
    differentialCommonCountertermCancellationStillValid : Bool
    absoluteNormalizationCanBeShiftedBeforeGravityConvention : Bool

canonicalVacuumNormalizationGravityBoundary :
  VacuumNormalizationGravityBoundary
canonicalVacuumNormalizationGravityBoundary =
  vacuum-normalization-gravity-boundary
    false false true true true true true true

normalizationConstantAloneDeterminesGravitationalStress : Bool
normalizationConstantAloneDeterminesGravitationalStress = false

sourceVacuumReadoutAloneDeterminesPhysicalLambda : Bool
sourceVacuumReadoutAloneDeterminesPhysicalLambda = false

renormalizedEffectiveActionMetricResponseRequired : Bool
renormalizedEffectiveActionMetricResponseRequired = true

gravitationalCosmologicalRenormalizationConditionRequired : Bool
gravitationalCosmologicalRenormalizationConditionRequired = true

differentialCommonCountertermCancellationStillValid : Bool
differentialCommonCountertermCancellationStillValid = true
