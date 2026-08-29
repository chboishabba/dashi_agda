module DASHI.Planning.SequentialPlanningPolicyBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Planning.CollectiveTerritorialConsentExact as Consent
import DASHI.Planning.NonSubstitutionalReparationExact as Repair

------------------------------------------------------------------------
-- SEQUENTIAL PLANNING POLICY BRIDGE
--
-- Thin socket aligned with PR #640's terminal obligations.  It deliberately
-- does not duplicate the sequential planner while #640 remains outside this
-- branch ancestry.
------------------------------------------------------------------------

record PlanningTerminalGate
    {State Model Action : Set}
    (live : State → Set)
    (robust : Action → State → Set)
    (decisionAdequate : Model → Action → Set)
    (authority : Action → Set)
    (consent : Action → Set)
    (repairClosed : Action → Set)
    (model : Model)
    (action : Action) : Set₁ where
  constructor planningTerminalGate
  field
    robustAcrossLive : (state : State) → live state → robust action state
    modelAdequate : decisionAdequate model action
    authorised : authority action
    consentSatisfied : consent action
    reparativeResidualClosed : repairClosed action

open PlanningTerminalGate public

data RobustnessAloneImpliesPlanningTerminalPermission : Set where
robustnessAloneCannotClosePlanning :
  RobustnessAloneImpliesPlanningTerminalPermission → ⊥
robustnessAloneCannotClosePlanning ()

data ModelAdequacyImpliesAuthorityPermission : Set where
modelAdequacyCannotCreateAuthority :
  ModelAdequacyImpliesAuthorityPermission → ⊥
modelAdequacyCannotCreateAuthority ()

data AuthorityImpliesConsentPermission : Set where
authorityCannotCreateConsent : AuthorityImpliesConsentPermission → ⊥
authorityCannotCreateConsent ()

record SequentialPlanningBridgeBoundary : Set where
  constructor sequentialPlanningBridgeBoundary
  field
    robustActionMayIgnoreConsent : Bool
    robustActionMayIgnoreConsentIsFalse : robustActionMayIgnoreConsent ≡ false
    modelAdequacyMayIgnoreAuthority : Bool
    modelAdequacyMayIgnoreAuthorityIsFalse : modelAdequacyMayIgnoreAuthority ≡ false
    closedInstitutionalModelMayIgnoreRepairResidual : Bool
    closedInstitutionalModelMayIgnoreRepairResidualIsFalse :
      closedInstitutionalModelMayIgnoreRepairResidual ≡ false

canonicalSequentialPlanningBridgeBoundary : SequentialPlanningBridgeBoundary
canonicalSequentialPlanningBridgeBoundary =
  sequentialPlanningBridgeBoundary false refl false refl false refl
