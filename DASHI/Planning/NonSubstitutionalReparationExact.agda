module DASHI.Planning.NonSubstitutionalReparationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- NON-SUBSTITUTIONAL REPARATION
--
-- Repair is multi-axis.  Closure on one axis cannot discharge an unresolved
-- obligation on another.  The structure is intentionally generic: land,
-- authority, decision rights, material compensation, truth and institutional
-- reform can be instantiated by source-specific legal/political modules.
------------------------------------------------------------------------

data RepairAxis : Set where
  acknowledgementAxis : RepairAxis
  truthAxis : RepairAxis
  restitutionAxis : RepairAxis
  landReturnAxis : RepairAxis
  compensationAxis : RepairAxis
  institutionalReformAxis : RepairAxis
  authorityRestorationAxis : RepairAxis
  decisionRightsAxis : RepairAxis
  nonRepetitionAxis : RepairAxis


data RepairStatus : Set where
  unrepaired : RepairStatus
  repaired : RepairStatus

record ReparativeBundle : Set where
  constructor reparativeBundle
  field
    status : RepairAxis → RepairStatus

apologyOnly : ReparativeBundle
apologyOnly = reparativeBundle apologyStatus
  where
  apologyStatus : RepairAxis → RepairStatus
  apologyStatus acknowledgementAxis = repaired
  apologyStatus truthAxis = unrepaired
  apologyStatus restitutionAxis = unrepaired
  apologyStatus landReturnAxis = unrepaired
  apologyStatus compensationAxis = unrepaired
  apologyStatus institutionalReformAxis = unrepaired
  apologyStatus authorityRestorationAxis = unrepaired
  apologyStatus decisionRightsAxis = unrepaired
  apologyStatus nonRepetitionAxis = unrepaired

compensationOnly : ReparativeBundle
compensationOnly = reparativeBundle compensationStatus
  where
  compensationStatus : RepairAxis → RepairStatus
  compensationStatus acknowledgementAxis = unrepaired
  compensationStatus truthAxis = unrepaired
  compensationStatus restitutionAxis = unrepaired
  compensationStatus landReturnAxis = unrepaired
  compensationStatus compensationAxis = repaired
  compensationStatus institutionalReformAxis = unrepaired
  compensationStatus authorityRestorationAxis = unrepaired
  compensationStatus decisionRightsAxis = unrepaired
  compensationStatus nonRepetitionAxis = unrepaired

apologyDoesNotRepairLandReturn :
  ReparativeBundle.status apologyOnly landReturnAxis ≡ repaired → ⊥
apologyDoesNotRepairLandReturn ()

compensationDoesNotRestoreAuthority :
  ReparativeBundle.status compensationOnly authorityRestorationAxis ≡ repaired → ⊥
compensationDoesNotRestoreAuthority ()

compensationDoesNotCreateDecisionRights :
  ReparativeBundle.status compensationOnly decisionRightsAxis ≡ repaired → ⊥
compensationDoesNotCreateDecisionRights ()

record NonSubstitutionBoundary : Set where
  constructor nonSubstitutionBoundary
  field
    apologyImpliesReparativeClosure : Bool
    apologyImpliesReparativeClosureIsFalse : apologyImpliesReparativeClosure ≡ false
    compensationSubstitutesForLandReturn : Bool
    compensationSubstitutesForLandReturnIsFalse :
      compensationSubstitutesForLandReturn ≡ false
    compensationSubstitutesForAuthorityRestoration : Bool
    compensationSubstitutesForAuthorityRestorationIsFalse :
      compensationSubstitutesForAuthorityRestoration ≡ false
    recognitionSubstitutesForSovereigntySettlement : Bool
    recognitionSubstitutesForSovereigntySettlementIsFalse :
      recognitionSubstitutesForSovereigntySettlement ≡ false
    representationSubstitutesForDecisionPower : Bool
    representationSubstitutesForDecisionPowerIsFalse :
      representationSubstitutesForDecisionPower ≡ false

canonicalNonSubstitutionBoundary : NonSubstitutionBoundary
canonicalNonSubstitutionBoundary =
  nonSubstitutionBoundary false refl false refl false refl false refl false refl

-- A non-substitutable loss can remain permanently unrecoverable even while
-- other relational/institutional axes remain repairable.
record IrreversibleLossBoundary : Set where
  constructor irreversibleLossBoundary
  field
    physicalRestorationPossible : Bool
    compensationCountsAsPhysicalRestoration : Bool
    relationalRepairMayRemainPossible : Bool

canonicalIrreversibleLossBoundary : IrreversibleLossBoundary
canonicalIrreversibleLossBoundary = irreversibleLossBoundary false false true
