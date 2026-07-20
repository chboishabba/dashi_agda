module DASHI.Philosophy.RepairAdmissibility where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.RepairCalculus as Repair

------------------------------------------------------------------------
-- Repair stages have admissibility constraints. Restitution without cessation
-- does not close repair; trust restoration is neither automatic nor required.

data RepairAdmissibility : Repair.RepairStage → Set where
  acknowledgeAdmissible : RepairAdmissibility Repair.acknowledgement
  ceaseHarmAdmissible : RepairAdmissibility Repair.cessationOfHarm
  restitutionAfterCessationAdmissible : RepairAdmissibility Repair.restitution
  institutionalChangeAdmissible : RepairAdmissibility Repair.institutionalChange
  trustAssessmentAdmissible : RepairAdmissibility Repair.trustAssessment
  coexistenceAdmissible : RepairAdmissibility Repair.coexistenceWithoutIntimacy
  irreparableLossRecognitionAdmissible :
    RepairAdmissibility Repair.irreparableLossRecognition

record RepairOrderingReceipt : Set₁ where
  field
    acknowledgementPresent : Set
    cessationPrecedesRestitution : Set
    restitutionPrecedesClosureClaim : Set
    institutionalChangeChecked : Set
    trustSeparatelyAssessed : Set
    coexistenceCanBeTerminal : Set
    irreparableLossModifiesObligations : Set

open RepairOrderingReceipt public

record RepairAdmissibilityBoundary : Set where
  constructor repairAdmissibilityBoundary
  field
    restitutionWithoutCessationValid : Bool
    restoredTrustAutomatic : Bool
    restoredIntimacyRequired : Bool
    coexistenceCanBeTerminalRepair : Bool
    irreparableLossEndsAllObligation : Bool
    irreparableLossChangesLaterObligation : Bool

open RepairAdmissibilityBoundary public

canonicalRepairAdmissibilityBoundary : RepairAdmissibilityBoundary
canonicalRepairAdmissibilityBoundary =
  repairAdmissibilityBoundary
    false
    false
    false
    true
    false
    true

canonicalRestitutionWithoutCessationInvalid :
  restitutionWithoutCessationValid canonicalRepairAdmissibilityBoundary
  ≡ false
canonicalRestitutionWithoutCessationInvalid = refl
