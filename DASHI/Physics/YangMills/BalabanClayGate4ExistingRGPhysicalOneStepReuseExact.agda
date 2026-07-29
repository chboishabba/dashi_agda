module DASHI.Physics.YangMills.BalabanClayGate4ExistingRGPhysicalOneStepReuseExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as PhysicalT5
import DASHI.Physics.YangMills.BalabanClayLegacyGaugeRGMeasureReuseExact as Legacy
import DASHI.Physics.YangMills.BalabanClayGate4CombinedSmallLargeNormAssemblyExact as Combined
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalOneStepClosureExact as PhysicalStep

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- This module is an adapter over the existing one-step RG and physical T5
-- defect carriers. It deliberately does not create a second RG transform.
------------------------------------------------------------------------

record ExistingRGPhysicalOneStepReuse
    {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Cutoff Observable DefectTerm : Set}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density)
    (defect : PhysicalT5.OneStepRGDefect Cutoff Observable DefectTerm) : Set₁ where
  field
    physicalIdentification :
      PhysicalStep.PhysicalOneStepIdentification
        {BoundaryTerm = BoundaryTerm} rg

    defectAdapter :
      Legacy.ExistingRGToT5DefectAdapter
        Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
        Bound Density Cutoff Observable DefectTerm rg defect

open ExistingRGPhysicalOneStepReuse public

physicalCombinedNormFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Cutoff Observable DefectTerm}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.OneStepRGDefect Cutoff Observable DefectTerm} →
  (reuse : ExistingRGPhysicalOneStepReuse
    {BoundaryTerm = BoundaryTerm} rg defect) →
  ExistingRG.LessEqual rg
    (ExistingRG.polymerNorm rg
      (PhysicalStep.combinedPolymer
        (PhysicalStep.next (physicalIdentification reuse))))
    (ExistingRG.addBound rg
      (ExistingRG.multiplyBound rg
        (ExistingRG.lambdaPolymer rg)
        (ExistingRG.polymerNorm rg
          (PhysicalStep.smallFieldPolymer
            (PhysicalStep.current (physicalIdentification reuse)))))
      (ExistingRG.addBound rg
        (ExistingRG.perturbativeError rg)
        (Combined.totalLargeFieldError
          (PhysicalStep.combinedBridge (physicalIdentification reuse)))))
physicalCombinedNormFromExistingRG reuse =
  PhysicalStep.physicalCombinedPolymerNormBound
    (physicalIdentification reuse)

physicalFluctuationGaugeInvarianceFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Cutoff Observable DefectTerm}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.OneStepRGDefect Cutoff Observable DefectTerm}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  ExistingRG.FluctuationIntegralGaugeInvariant rg
physicalFluctuationGaugeInvarianceFromExistingRG {rg = rg} reuse =
  Legacy.existingFluctuationIntegralGaugeInvariant rg

physicalEffectiveWardFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Cutoff Observable DefectTerm}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.OneStepRGDefect Cutoff Observable DefectTerm}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  ExistingRG.EffectiveActionWardIdentity rg
physicalEffectiveWardFromExistingRG {rg = rg} reuse =
  Legacy.existingEffectiveActionWardIdentity rg

physicalLocalizationWardFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Cutoff Observable DefectTerm}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.OneStepRGDefect Cutoff Observable DefectTerm}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  ExistingRG.LocalizationPreservesWardIdentity rg
physicalLocalizationWardFromExistingRG {rg = rg} reuse =
  Legacy.existingLocalizationPreservesWardIdentity rg

physicalCountertermCancellationFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Cutoff Observable DefectTerm}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.OneStepRGDefect Cutoff Observable DefectTerm}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  ExistingRG.VacuumCountertermCancelsLocalConstant rg
physicalCountertermCancellationFromExistingRG {rg = rg} reuse =
  Legacy.existingVacuumCountertermCancellation rg

physicalCouplingRenormalizationFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Cutoff Observable DefectTerm}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.OneStepRGDefect Cutoff Observable DefectTerm}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  ExistingRG.CouplingRenormalization rg
physicalCouplingRenormalizationFromExistingRG {rg = rg} reuse =
  Legacy.existingCouplingRenormalization rg

physicalIrrelevantContractionFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Cutoff Observable DefectTerm}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.OneStepRGDefect Cutoff Observable DefectTerm}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  ExistingRG.IrrelevantTaylorRemainderContractive rg
physicalIrrelevantContractionFromExistingRG {rg = rg} reuse =
  Legacy.existingIrrelevantTaylorContraction rg

existingRGPhysicalOneStepReuseLevel : ProofLevel
existingRGPhysicalOneStepReuseLevel = machineChecked

physicalCombinedNormExistingRGReuseLevel : ProofLevel
physicalCombinedNormExistingRGReuseLevel = machineChecked

physicalGaugeWardCountertermReuseLevel : ProofLevel
physicalGaugeWardCountertermReuseLevel = machineChecked

physicalCouplingIrrelevantReuseLevel : ProofLevel
physicalCouplingIrrelevantReuseLevel = machineChecked

physicalRGDefectRepresentationInputsLevel : ProofLevel
physicalRGDefectRepresentationInputsLevel = conditional

physicalInvariantDomainAndBoundaryInputsLevel : ProofLevel
physicalInvariantDomainAndBoundaryInputsLevel = conditional
