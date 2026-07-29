module DASHI.Physics.YangMills.BalabanClayLegacyGaugeRGMeasureReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPath4SU2FullGaugeFixedCoercivityExact as Gauge
import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as RG
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5PhysicalTailMomentMeasureClosureExact as Closure
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5LpUniformIntegrabilityExact as Lp
import DASHI.Physics.YangMills.BalabanClayT5LpPhysicalMeasureAdapterExact as LpAdapter
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as Thermo

------------------------------------------------------------------------
-- Reuse adapters for the pre-existing gauge, RG and measure machinery.
--
-- This module prevents the literal T4--T5 closure tranche from being read as a
-- second implementation of structures already present in DASHI.  It exposes the
-- existing gauge-fixed coercivity theorem, one-step RG Ward/counterterm/coupling
-- witnesses and physical-measure-to-OS-Gram adapter, then records only the exact
-- representation seams that must be discharged to reuse them.
------------------------------------------------------------------------

-- Existing unconditional gauge-fixed result.  No new gauge coercivity authority
-- is introduced by the T4 Ward certificate lane.
reusedFullGaugeFixedResidualDecomposition =
  Gauge.fullGaugeFixedResidualDecompositionExact

reusedFullGaugeFixedCoercivity = Gauge.fullGaugeFixedCoercivity

-- Existing one-step RG witnesses.  These are projections from the already-built
-- OneStepRGCutset, not fresh T5 assumptions.
existingFluctuationIntegralGaugeInvariant :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : RG.OneStepRGCutset
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density) →
  RG.FluctuationIntegralGaugeInvariant rg
existingFluctuationIntegralGaugeInvariant = RG.fluctuationIntegralGaugeInvariant

existingEffectiveActionWardIdentity :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : RG.OneStepRGCutset
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density) →
  RG.EffectiveActionWardIdentity rg
existingEffectiveActionWardIdentity = RG.effectiveActionWardIdentity

existingLocalizationPreservesWardIdentity :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : RG.OneStepRGCutset
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density) →
  RG.LocalizationPreservesWardIdentity rg
existingLocalizationPreservesWardIdentity = RG.localizationPreservesWardIdentity

existingVacuumCountertermCancellation :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : RG.OneStepRGCutset
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density) →
  RG.VacuumCountertermCancelsLocalConstant rg
existingVacuumCountertermCancellation = RG.vacuumCountertermCancelsLocalConstant

existingCouplingRenormalization :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : RG.OneStepRGCutset
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density) →
  RG.CouplingRenormalization rg
existingCouplingRenormalization = RG.couplingRenormalization

existingIrrelevantTaylorContraction :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density}
    (rg : RG.OneStepRGCutset
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density) →
  RG.IrrelevantTaylorRemainderContractive rg
existingIrrelevantTaylorContraction = RG.irrelevantTaylorRemainderContractive

record ExistingRGToT5DefectAdapter
    (Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
     Bound Density Cutoff Observable DefectTerm : Set)
    (rg : RG.OneStepRGCutset
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density)
    (defect : Physical.OneStepRGDefect Cutoff Observable DefectTerm) : Set₁ where
  field
    blockedObservableIsExistingRGObservableTransform :
      (cutoff : Cutoff) → (observable : Observable) → Set
    defectExpansionIsExistingLocalizedPolymerRemainder :
      (cutoff : Cutoff) → (observable : Observable) → Set

    relevantCancellationUsesWardAndRenormalization :
      (cutoff : Cutoff) → (observable : Observable) → Set
    vacuumPartUsesExistingCountertermCancellation : Set
    couplingPartUsesExistingYangMillsBetaFlow : Set

    irrelevantTermsUseExistingTaylorContraction :
      (cutoff : Cutoff) → (observable : Observable) →
      (term : DefectTerm) → Set
    localizationSupportAndWeightAreReused : Set
    quantitativeScaleGainSpecializesExistingPolymerContraction :
      (cutoff : Cutoff) → (observable : Observable) → Set

    noDuplicateOneStepRGAuthority : Set

open ExistingRGToT5DefectAdapter public

record ExistingGaugeRGMeasureReuse
    (Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
     Bound Density Cutoff Observable DefectTerm
     Volume Boundary Cluster Block Dimension Marginal Measure Index Scalar : Set)
    (rg : RG.OneStepRGCutset
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density)
    (defect : Physical.OneStepRGDefect Cutoff Observable DefectTerm) : Set₂ where
  field
    rgToT5 : ExistingRGToT5DefectAdapter
      Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density Cutoff Observable DefectTerm rg defect

    physicalClosure :
      Physical.PhysicalT5Closure
        Volume Boundary Observable Polymer Cluster Block Cutoff DefectTerm
        Dimension Marginal Measure Index

    literalClosure :
      Closure.LiteralPhysicalT5Completion
        Volume Boundary Observable Polymer Cluster Block Cutoff DefectTerm
        Dimension Marginal Measure Index

    physicalAndLiteralClusterExpansionsAgree : Set
    physicalAndLiteralRGDefectsAgree : Set
    physicalAndLiteralMarkedMomentsAgree : Set
    physicalAndLiteralContinuumMeasuresAgree : Set

    physicalExpectationProducer :
      Thermo.PhysicalExpectationProducerData Measure Observable Scalar
    lpUniformIntegrabilityUpgrade :
      Lp.LpExpectationProducerUpgrade physicalExpectationProducer

    lpPhysicalMeasureAdapter :
      LpAdapter.LpPhysicalMeasureToOSGramData lpUniformIntegrabilityUpgrade
    physicalMeasureToGram :
      Gram.PhysicalMeasureToOSGramData Measure Observable Scalar
    physicalMeasureToGramUsesLpAdapter :
      physicalMeasureToGram
      ≡ LpAdapter.lpPhysicalMeasureToGramData lpPhysicalMeasureAdapter
    gramConvergenceConsumesLpUniformIntegrability :
      Gram.convergenceData physicalMeasureToGram
      ≡ LpAdapter.lpPhysicalMeasureConvergenceData
          lpUniformIntegrabilityUpgrade

    gaugeFixedCoercivityFeedsCriticalMapRadius : Set
    wardCertificateNormalizesToExistingWardIdentity : Set
    continuumMeasureCarriesExistingOSGramLimit : Set

open ExistingGaugeRGMeasureReuse public

record ExistingLpReuseReceipt
    {Measure Observable Scalar : Set}
    {producer :
      Thermo.PhysicalExpectationProducerData
        Measure Observable Scalar}
    (upgrade : Lp.LpExpectationProducerUpgrade producer) : Set₁ where
  field
    lpGramAdapter : LpAdapter.LpPhysicalMeasureToOSGramData upgrade
    convergenceData : Gram.PhysicalMeasureConvergenceData Measure Observable Scalar
    convergenceDataExact :
      convergenceData ≡ LpAdapter.lpPhysicalMeasureConvergenceData upgrade
    gramDataExact :
      LpAdapter.lpPhysicalMeasureToGramData lpGramAdapter
      ≡ LpAdapter.lpPhysicalMeasureToGramData lpGramAdapter
    existingPhysicalExpectationAdapterUsed : Set
    existingOSGramFiniteSumAdapterUsed : Set

open ExistingLpReuseReceipt public

gaugeReuseLevel : ProofLevel
gaugeReuseLevel = machineChecked

oneStepRGWitnessReuseLevel : ProofLevel
oneStepRGWitnessReuseLevel = machineChecked

physicalMeasureOSGramReuseLevel : ProofLevel
physicalMeasureOSGramReuseLevel = machineChecked

rgToT5RepresentationSeamLevel : ProofLevel
rgToT5RepresentationSeamLevel = conditional

physicalMeasureAgreementSeamLevel : ProofLevel
physicalMeasureAgreementSeamLevel = conditional
