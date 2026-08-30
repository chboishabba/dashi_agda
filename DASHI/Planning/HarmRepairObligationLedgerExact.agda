module DASHI.Planning.HarmRepairObligationLedgerExact where

open import DASHI.Core.Prelude
import DASHI.Planning.NonSubstitutionalReparationExact as Repair

------------------------------------------------------------------------
-- HARM -> REPAIR OBLIGATION LEDGER
------------------------------------------------------------------------

data HarmAxis : Set where
  dispossessionHarm exclusionFromDecisionHarm institutionalAbuseHarm
  irreversibleDestructionHarm : HarmAxis

Obliges : HarmAxis → Repair.RepairAxis → Set
Obliges dispossessionHarm Repair.restitutionAxis = ⊤
Obliges dispossessionHarm Repair.landReturnAxis = ⊤
Obliges dispossessionHarm Repair.authorityRestorationAxis = ⊤
Obliges exclusionFromDecisionHarm Repair.decisionRightsAxis = ⊤
Obliges exclusionFromDecisionHarm Repair.authorityRestorationAxis = ⊤
Obliges institutionalAbuseHarm Repair.institutionalReformAxis = ⊤
Obliges institutionalAbuseHarm Repair.nonRepetitionAxis = ⊤
Obliges irreversibleDestructionHarm Repair.truthAxis = ⊤
Obliges irreversibleDestructionHarm Repair.nonRepetitionAxis = ⊤
Obliges _ _ = ⊥

record ObligationDischarged
    (bundle : Repair.ReparativeBundle)
    (harm : HarmAxis)
    (axis : Repair.RepairAxis) : Set where
  constructor obligationDischarged
  field
    obligationExists : Obliges harm axis
    axisRepaired : Repair.ReparativeBundle.status bundle axis ≡ Repair.repaired

open ObligationDischarged public

compensationDoesNotDischargeDispossessionLandReturn :
  ObligationDischarged Repair.compensationOnly dispossessionHarm Repair.landReturnAxis → ⊥
compensationDoesNotDischargeDispossessionLandReturn discharged =
  compensationOnlyLandOpen (axisRepaired discharged)
  where
  compensationOnlyLandOpen :
    Repair.ReparativeBundle.status Repair.compensationOnly Repair.landReturnAxis ≡ Repair.repaired → ⊥
  compensationOnlyLandOpen ()

apologyDoesNotDischargeDecisionExclusion :
  ObligationDischarged Repair.apologyOnly exclusionFromDecisionHarm Repair.decisionRightsAxis → ⊥
apologyDoesNotDischargeDecisionExclusion discharged = axisStillOpen (axisRepaired discharged)
  where
  axisStillOpen :
    Repair.ReparativeBundle.status Repair.apologyOnly Repair.decisionRightsAxis ≡ Repair.repaired → ⊥
  axisStillOpen ()

record ObligationLedgerBoundary : Set where
  constructor obligationLedgerBoundary
  field
    unrelatedRepairAxisDischargesObligation : Bool
    unrelatedRepairAxisDischargesObligationIsFalse :
      unrelatedRepairAxisDischargesObligation ≡ false
    irreversibleLossErasesSurvivingObligations : Bool
    irreversibleLossErasesSurvivingObligationsIsFalse :
      irreversibleLossErasesSurvivingObligations ≡ false

canonicalObligationLedgerBoundary : ObligationLedgerBoundary
canonicalObligationLedgerBoundary = obligationLedgerBoundary false refl false refl
