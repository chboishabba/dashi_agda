module DASHI.Physics.YangMills.BalabanClayGate4ExistingRGPhysicalOneStepReuseExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG
import DASHI.Physics.YangMills.BalabanClayT5PhysicalRGClosureExact as PhysicalT5
import DASHI.Physics.YangMills.BalabanClayLegacyGaugeRGMeasureReuseExact as Legacy
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
-- defect carriers.  It deliberately does not create a second RG transform.
------------------------------------------------------------------------

record ExistingRGPhysicalOneStepReuse
    {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Observable Defect : Set}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density)
    (defect : PhysicalT5.PhysicalRGDefectClosure Observable Defect) : Set₁ where
  field
    physicalIdentification :
      PhysicalStep.PhysicalOneStepIdentification
        {BoundaryTerm = BoundaryTerm} rg

    defectAdapter : Legacy.ExistingRGToT5DefectAdapter rg defect

open ExistingRGPhysicalOneStepReuse public

physicalCombinedNormFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Observable Defect}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.PhysicalRGDefectClosure Observable Defect} →
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
        (DASHI.Physics.YangMills.BalabanClayGate4CombinedSmallLargeNormAssemblyExact.totalLargeFieldError
          (PhysicalStep.combinedBridge (physicalIdentification reuse)))))
physicalCombinedNormFromExistingRG reuse =
  PhysicalStep.physicalCombinedPolymerNormBound
    (physicalIdentification reuse)

physicalFluctuationGaugeInvarianceFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Observable Defect}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.PhysicalRGDefectClosure Observable Defect}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  Legacy.FluctuationIntegralGaugeInvariant (defectAdapter reuse)
physicalFluctuationGaugeInvarianceFromExistingRG reuse =
  Legacy.reusedFluctuationGaugeInvariance (defectAdapter reuse)

physicalEffectiveWardFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Observable Defect}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.PhysicalRGDefectClosure Observable Defect}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  Legacy.EffectiveActionSatisfiesWard (defectAdapter reuse)
physicalEffectiveWardFromExistingRG reuse =
  Legacy.reusedEffectiveActionWard (defectAdapter reuse)

physicalLocalizationWardFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Observable Defect}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.PhysicalRGDefectClosure Observable Defect}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  Legacy.LocalizationSatisfiesWard (defectAdapter reuse)
physicalLocalizationWardFromExistingRG reuse =
  Legacy.reusedLocalizationWard (defectAdapter reuse)

physicalCountertermCancellationFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Observable Defect}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.PhysicalRGDefectClosure Observable Defect}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  Legacy.VacuumCountertermCancels (defectAdapter reuse)
physicalCountertermCancellationFromExistingRG reuse =
  Legacy.reusedVacuumCountertermCancellation (defectAdapter reuse)

physicalCouplingRenormalizationFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Observable Defect}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.PhysicalRGDefectClosure Observable Defect}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  Legacy.CouplingRenormalizes (defectAdapter reuse)
physicalCouplingRenormalizationFromExistingRG reuse =
  Legacy.reusedCouplingRenormalization (defectAdapter reuse)

physicalIrrelevantContractionFromExistingRG :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density BoundaryTerm Observable Defect}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {defect : PhysicalT5.PhysicalRGDefectClosure Observable Defect}
    (reuse : ExistingRGPhysicalOneStepReuse
      {BoundaryTerm = BoundaryTerm} rg defect) →
  Legacy.IrrelevantRemainderContracts (defectAdapter reuse)
physicalIrrelevantContractionFromExistingRG reuse =
  Legacy.reusedIrrelevantContraction (defectAdapter reuse)

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
