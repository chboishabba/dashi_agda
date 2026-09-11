module DASHI.Physics.Chemistry.AtomicPeriodicTable369PhysicalValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369Validation as Structural
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ArchiveHartreeRadialIdentityDefectExact as Defect
import DASHI.Physics.Chemistry.AtomicPeriodicTable369RadialIdentityRepairExecutionExact as Repair
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HydrogenNISTComparisonExact as HN
import DASHI.Physics.Chemistry.AtomicPeriodicTable369HydrogenReducedMassExact as HR

------------------------------------------------------------------------
-- Focused physical validation root.
--
-- This composes the structural periodic-table validation root with the exact
-- archive Hartree defect, the executed n-sensitive radial repair receipt, the
-- first external NIST reference-data diagnostic, and the leading finite-proton
-- reduced-mass correction. Keeping them in one cone prevents later numerical
-- evidence from silently rewriting earlier source or implementation state.
------------------------------------------------------------------------

archiveDefectRegression :
  Defect.ArchiveHartreeDefectBoundary.repairedNSensitiveSelectorRequired
    Defect.canonicalArchiveHartreeDefectBoundary
  ≡ true
  ×
  Defect.ArchiveHartreeDefectBoundary.sameLTargetCollapsePreservesPrincipalIdentity
    Defect.canonicalArchiveHartreeDefectBoundary
  ≡ false
archiveDefectRegression = refl , refl

repairExecutionRegression :
  Repair.RadialIdentityExecutionReceipt.sameLPrincipalIdentityDistinguished
    Repair.canonicalRadialIdentityExecutionReceipt
  ≡ true
  ×
  Repair.RadialIdentityExecutionReceipt.hydrogenicEnergyChecksPassed
    Repair.canonicalRadialIdentityExecutionReceipt
  ≡ true
  ×
  Repair.RadialIdentityExecutionReceipt.radialNodeChecksPassed
    Repair.canonicalRadialIdentityExecutionReceipt
  ≡ true
  ×
  Repair.RadialIdentityExecutionReceipt.orthogonalityChecksPassed
    Repair.canonicalRadialIdentityExecutionReceipt
  ≡ true
  ×
  Repair.RadialIdentityExecutionReceipt.overallPassed
    Repair.canonicalRadialIdentityExecutionReceipt
  ≡ true
repairExecutionRegression = refl , (refl , (refl , (refl , refl)))

sameObjectPromotionBoundaryRegression :
  Repair.DefectRepairWeld.radialIdentityExecutionPaid
    Repair.canonicalDefectRepairWeld
  ≡ true
  ×
  Repair.DefectRepairWeld.scfStateTrackingPaid
    Repair.canonicalDefectRepairWeld
  ≡ false
  ×
  Repair.DefectRepairWeld.manyElectronSpectrumPaid
    Repair.canonicalDefectRepairWeld
  ≡ false
  ×
  Repair.DefectRepairWeld.calibratedIonizationPaid
    Repair.canonicalDefectRepairWeld
  ≡ false
sameObjectPromotionBoundaryRegression = refl , (refl , (refl , refl))

referenceDataBoundaryRegression :
  Repair.RadialIdentityRepairBoundary.nistDatabasePresenceImpliesAgreement
    Repair.canonicalRadialIdentityRepairBoundary
  ≡ false
  ×
  Repair.RadialIdentityRepairBoundary.sameObjectSCFProducerStillNeeded
    Repair.canonicalRadialIdentityRepairBoundary
  ≡ true
referenceDataBoundaryRegression = refl , refl

hydrogenNISTExecutionRegression :
  HN.HydrogenReferenceComparisonReceipt.comparisonExecuted
    HN.canonicalHydrogenReferenceComparisonReceipt
  ≡ true
  ×
  HN.HydrogenComparisonBoundary.oneElectronReferenceDiagnosticPaid
    HN.canonicalHydrogenComparisonBoundary
  ≡ true
hydrogenNISTExecutionRegression = refl , refl

hydrogenNISTNonPromotionRegression :
  HN.HydrogenComparisonBoundary.numericResidualCloserThanAnalyticImpliesBetterPhysics
    HN.canonicalHydrogenComparisonBoundary
  ≡ false
  ×
  HN.HydrogenComparisonBoundary.numericalDiscretizationErrorSeparatedFromModelError
    HN.canonicalHydrogenComparisonBoundary
  ≡ false
  ×
  HN.HydrogenComparisonBoundary.finiteProtonMassPaid
    HN.canonicalHydrogenComparisonBoundary
  ≡ false
  ×
  HN.HydrogenComparisonBoundary.manyElectronSCFPaid
    HN.canonicalHydrogenComparisonBoundary
  ≡ false
  ×
  HN.HydrogenComparisonBoundary.periodicTableEmpiricalRecoveryPaid
    HN.canonicalHydrogenComparisonBoundary
  ≡ false
hydrogenNISTNonPromotionRegression =
  refl , (refl , (refl , (refl , refl)))

hydrogenReducedMassExecutionRegression :
  HR.ReducedMassExecutionReceipt.residualMagnitudeImprovesOverInfiniteMass
    HR.canonicalReducedMassExecutionReceipt
  ≡ true
  ×
  HR.ReducedMassExecutionReceipt.executionPaid
    HR.canonicalReducedMassExecutionReceipt
  ≡ true
  ×
  HR.HydrogenCorrectionBudget.finiteProtonReducedMassPaid
    HR.canonicalHydrogenCorrectionBudget
  ≡ true
hydrogenReducedMassExecutionRegression = refl , (refl , refl)

hydrogenCorrectionBudgetRegression :
  HR.HydrogenCorrectionBudget.relativisticCorrectionPaid
    HR.canonicalHydrogenCorrectionBudget
  ≡ false
  ×
  HR.HydrogenCorrectionBudget.radiativeQEDPaid
    HR.canonicalHydrogenCorrectionBudget
  ≡ false
  ×
  HR.HydrogenCorrectionBudget.nistAgreementWithinQuotedUncertaintyPaid
    HR.canonicalHydrogenCorrectionBudget
  ≡ false
  ×
  HR.HydrogenCorrectionBudget.manyElectronGeneralityPaid
    HR.canonicalHydrogenCorrectionBudget
  ≡ false
hydrogenCorrectionBudgetRegression = refl , (refl , (refl , refl))

-- The Structural import is intentionally retained even though no name is used
-- below: importing the module is what keeps the structural validation root in
-- the same Agda checker cone as this physical evidence layer.
