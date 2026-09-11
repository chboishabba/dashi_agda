module DASHI.Physics.Chemistry.AtomicPeriodicTable369PhysicalValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369Validation as Structural
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ArchiveHartreeRadialIdentityDefectExact as Defect
import DASHI.Physics.Chemistry.AtomicPeriodicTable369RadialIdentityRepairExecutionExact as Repair

------------------------------------------------------------------------
-- Focused physical validation root.
--
-- This composes the structural periodic-table validation root with the exact
-- archive Hartree defect and the first executed n-sensitive repair receipt.
-- Checking this module therefore keeps the defect and repair in the same
-- checker cone instead of letting a later producer silently replace history.
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

-- Import witness that the pre-existing structural root remains in this cone.
structuralValidationOwner : Set
structuralValidationOwner = Structural.CrossRepoRegressionDiscipline
