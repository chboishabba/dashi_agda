{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumExtensivityMetricResponseExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Closure.SymbolicEinsteinHilbertModel as EH

------------------------------------------------------------------------
-- VACUUM CONSTANT -> VACUUM DENSITY REQUIRES AN EXTENSIVITY / VOLUME WELD
--
-- A scalar additive constant in a finite action is not, merely by being named
-- "vacuum energy", a gravitational source.  The cosmological stress target is
-- produced by a LOCAL/EXTENSIVE vacuum density integrated against the metric
-- volume element.  At first order the relevant algebra is
--
--   S_vac[g] = v * Vol[g]
--   D_h S_vac = v * D_h Vol[g].
--
-- Hence a metric-independent additive scalar has zero metric variation.  The
-- source programme must identify the recovered CMP119 scalar with the density
-- coefficient of the SAME metric-volume family before the symbolic EH vacuum
-- variation can be consumed as a physical stress theorem.
------------------------------------------------------------------------

record ExtensiveVacuumMetricFamily : Set where
  constructor extensive-vacuum-metric-family
  field
    vacuumDensityCoefficient : ℚ
    referenceVolume : ℚ
    volumeVariation : K.SymmetricTensorComponent4 → ℚ

open ExtensiveVacuumMetricFamily public

vacuumAction : ExtensiveVacuumMetricFamily → ℚ
vacuumAction family =
  vacuumDensityCoefficient family * referenceVolume family

vacuumActionVariation :
  ExtensiveVacuumMetricFamily → K.SymmetricTensorComponent4 → ℚ
vacuumActionVariation family h =
  vacuumDensityCoefficient family * volumeVariation family h

vacuumActionVariationIsDensityTimesVolumeVariation :
  ∀ family h →
  vacuumActionVariation family h
  ≡ vacuumDensityCoefficient family * volumeVariation family h
vacuumActionVariationIsDensityTimesVolumeVariation family h = refl

metricIndependentConstantHasZeroVariation :
  ∀ family →
  (∀ h → volumeVariation family h ≡ 0ℚ) →
  ∀ h → vacuumActionVariation family h ≡ 0ℚ
metricIndependentConstantHasZeroVariation family fixedVolume h
  rewrite fixedVolume h = refl

symbolicVacuumDensityVariationTarget :
  EH.varyInvariant EH.vacuumDensity ≡ EH.cosmologicalTensorTerm
symbolicVacuumDensityVariationTarget =
  EH.vacuumVariationIsCosmological

record VacuumExtensivityToCosmologicalStressReceipt
    (finiteVacuumScalar : ℚ) : Set₁ where
  field
    family : ExtensiveVacuumMetricFamily

    -- The recovered finite/source scalar is the density coefficient of this
    -- exact same metric family, not merely numerically similar.
    finiteScalarIsVacuumDensityCoefficient :
      finiteVacuumScalar ≡ vacuumDensityCoefficient family

    SameStateVacuumDensityReceipt : Set
    sameStateVacuumDensityReceipt : SameStateVacuumDensityReceipt

    MetricVolumeFamilyReceipt : Set
    metricVolumeFamilyReceipt : MetricVolumeFamilyReceipt

    -- This is where the finite lattice normalization / cell-volume convention
    -- is welded to the continuum/local density convention.
    LatticeToPhysicalVolumeNormalizationReceipt : Set
    latticeToPhysicalVolumeNormalizationReceipt :
      LatticeToPhysicalVolumeNormalizationReceipt

    CosmologicalRenormalizationConditionReceipt : Set
    cosmologicalRenormalizationConditionReceipt :
      CosmologicalRenormalizationConditionReceipt

open VacuumExtensivityToCosmologicalStressReceipt public

receiptVacuumVariation :
  ∀ {finiteVacuumScalar}
    (receipt : VacuumExtensivityToCosmologicalStressReceipt finiteVacuumScalar)
    h →
  vacuumActionVariation (family receipt) h
  ≡ finiteVacuumScalar * volumeVariation (family receipt) h
receiptVacuumVariation receipt h =
  cong
    (λ coefficient → coefficient * volumeVariation (family receipt) h)
    (sym (finiteScalarIsVacuumDensityCoefficient receipt))

record VacuumExtensivityMetricResponseBoundary : Set where
  constructor vacuum-extensivity-metric-response-boundary
  field
    finiteScalarAloneDeterminesCosmologicalStress : Bool
    extensiveVacuumDensityTargetShapeOwned : Bool
    metricIndependentConstantCanSourceCosmologicalStressByNameAlone : Bool
    extensivityVolumeWeldStillRequired : Bool
    latticeToPhysicalVolumeNormalizationStillRequired : Bool
    cosmologicalRenormalizationConditionStillRequired : Bool

canonicalVacuumExtensivityMetricResponseBoundary :
  VacuumExtensivityMetricResponseBoundary
canonicalVacuumExtensivityMetricResponseBoundary =
  vacuum-extensivity-metric-response-boundary
    false true false true true true

finiteScalarAloneDeterminesCosmologicalStress : Bool
finiteScalarAloneDeterminesCosmologicalStress = false

extensivityVolumeWeldStillRequired : Bool
extensivityVolumeWeldStillRequired = true

latticeToPhysicalVolumeNormalizationStillRequired : Bool
latticeToPhysicalVolumeNormalizationStillRequired = true
