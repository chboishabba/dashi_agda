module DASHI.Physics.Foundations.KernelEmergenceHypothesesExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as Geometry
import DASHI.Physics.Foundations.KernelQFTEmergenceObligations as Quantum

------------------------------------------------------------------------
-- Explicit conjectural hypotheses, typed separately from discharged theorems.

data HypothesisStatus : Set where
  conjecturalHypothesis : HypothesisStatus
  finiteAnalogueProved : HypothesisStatus
  continuumLimitProved : HypothesisStatus

record KernelGeometryHypothesis : Set where
  constructor kernelGeometryHypothesis
  field
    geometryAdapter : Geometry.KernelGeometryAdapter
    status : HypothesisStatus
    macroscopicErrorControlled : Bool

open KernelGeometryHypothesis public

currentKernelGeometryHypothesis : KernelGeometryHypothesis
currentKernelGeometryHypothesis =
  kernelGeometryHypothesis
    Geometry.currentKernelGeometryAdapter
    conjecturalHypothesis
    false

record KernelQFTHypothesis : Set where
  constructor kernelQFTHypothesis
  field
    qftAdapter : Quantum.KernelQFTAdapter
    status : HypothesisStatus
    irrelevantOperatorsControlled : Bool

open KernelQFTHypothesis public

currentKernelQFTHypothesis : KernelQFTHypothesis
currentKernelQFTHypothesis =
  kernelQFTHypothesis
    Quantum.currentKernelQFTAdapter
    conjecturalHypothesis
    false

------------------------------------------------------------------------
-- Finite correction-suppression model.

data ObservationScale : Set where
  microscopicScale : ObservationScale
  intermediateScale : ObservationScale
  macroscopicScale : ObservationScale

geometryCorrection : ObservationScale → Nat
geometryCorrection microscopicScale = 9
geometryCorrection intermediateScale = 3
geometryCorrection macroscopicScale = 1

qftIrrelevantCorrection : ObservationScale → Nat
qftIrrelevantCorrection microscopicScale = 8
qftIrrelevantCorrection intermediateScale = 2
qftIrrelevantCorrection macroscopicScale = 0

geometryCorrectionDecreasesAtMacroscopicScale :
  geometryCorrection macroscopicScale ≤ geometryCorrection microscopicScale
geometryCorrectionDecreasesAtMacroscopicScale = s≤s z≤n

qftCorrectionVanishesInFiniteMacroscopicExample :
  qftIrrelevantCorrection macroscopicScale ≡ 0
qftCorrectionVanishesInFiniteMacroscopicExample = refl

------------------------------------------------------------------------
-- Effective-action dominance is more than the appearance of a target term.

data EffectiveTerm : Set where
  einsteinHilbertTerm : EffectiveTerm
  standardModelTerm : EffectiveTerm
  correctionTerm : EffectiveTerm

termWeight : ObservationScale → EffectiveTerm → Nat
termWeight microscopicScale einsteinHilbertTerm = 1
termWeight microscopicScale standardModelTerm = 1
termWeight microscopicScale correctionTerm = 9
termWeight intermediateScale einsteinHilbertTerm = 3
termWeight intermediateScale standardModelTerm = 3
termWeight intermediateScale correctionTerm = 2
termWeight macroscopicScale einsteinHilbertTerm = 5
termWeight macroscopicScale standardModelTerm = 5
termWeight macroscopicScale correctionTerm = 1

macroscopicCorrectionIsSubdominantToGeometry :
  termWeight macroscopicScale correctionTerm
  ≤
  termWeight macroscopicScale einsteinHilbertTerm
macroscopicCorrectionIsSubdominantToGeometry = s≤s z≤n

macroscopicCorrectionIsSubdominantToMatter :
  termWeight macroscopicScale correctionTerm
  ≤
  termWeight macroscopicScale standardModelTerm
macroscopicCorrectionIsSubdominantToMatter = s≤s z≤n

record EffectiveRecoveryCriterion : Set where
  constructor effectiveRecoveryCriterion
  field
    geometryTargetPresent : Bool
    matterTargetPresent : Bool
    commonCoarseGraining : Bool
    correctionSuppression : Bool
    backreactionClosed : Bool

open EffectiveRecoveryCriterion public

currentEffectiveRecoveryCriterion : EffectiveRecoveryCriterion
currentEffectiveRecoveryCriterion =
  effectiveRecoveryCriterion true true false false false

record KernelEmergenceHypothesisBoundary : Set where
  constructor kernelEmergenceHypothesisBoundary
  field
    targetTermsPresentImpliesEffectiveRecovery : Bool
    targetTermsPresentImpliesEffectiveRecoveryIsFalse :
      targetTermsPresentImpliesEffectiveRecovery ≡ false

    finiteCorrectionTableProvesContinuumSuppression : Bool
    finiteCorrectionTableProvesContinuumSuppressionIsFalse :
      finiteCorrectionTableProvesContinuumSuppression ≡ false

    kernelGeometryHypothesisIsDischarged : Bool
    kernelGeometryHypothesisIsDischargedIsFalse :
      kernelGeometryHypothesisIsDischarged ≡ false

    kernelQFTHypothesisIsDischarged : Bool
    kernelQFTHypothesisIsDischargedIsFalse :
      kernelQFTHypothesisIsDischarged ≡ false

open KernelEmergenceHypothesisBoundary public

canonicalKernelEmergenceHypothesisBoundary :
  KernelEmergenceHypothesisBoundary
canonicalKernelEmergenceHypothesisBoundary =
  kernelEmergenceHypothesisBoundary false refl false refl false refl false refl
