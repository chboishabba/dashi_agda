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
  acknowledgementAxis
  truthAxis
  restitutionAxis
  landReturnAxis
  compensationAxis
  institutionalReformAxis
  authorityRestorationAxis
  decisionRightsAxis
  nonRepetitionAxis
  : RepairAxis

data RepairStatus : Set where
  open repaired : RepairStatus

record ReparativeBundle : Set where
  constructor reparativeBundle
  field
    status : RepairAxis → RepairStatus

apologyOnly : ReparativeBundle
apologyOnly = reparativeBundle apologyStatus
  where
  apologyStatus : RepairAxis → RepairStatus
  apologyStatus acknowledgementAxis = repaired
  apologyStatus truthAxis = open
  apologyStatus restitutionAxis = open
  apologyStatus landReturnAxis = open
  apologyStatus compensationAxis = open
  apologyStatus institutionalReformAxis = open
  apologyStatus authorityRestorationAxis = open
  apologyStatus decisionRightsAxis = open
  apologyStatus nonRepetitionAxis = open

compensationOnly : ReparativeBundle
compensationOnly = reparativeBundle compensationStatus
  where
  compensationStatus : RepairAxis → RepairStatus
  compensationStatus acknowledgementAxis = open
  compensationStatus truthAxis = open
  compensationStatus restitutionAxis = open
  compensationStatus landReturnAxis = open
  compensationStatus compensationAxis = repaired
  compensationStatus institutionalReformAxis = open
  compensationStatus authorityRestorationAxis = open
  compensationStatus decisionRightsAxis = open
  compensationStatus nonRepetitionAxis = open

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
