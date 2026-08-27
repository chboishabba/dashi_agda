module DASHI.Governance.ObserverValuationAuthoritySeparationExact where

------------------------------------------------------------------------
-- OBSERVER / VALUATION / AUTHORITY SEPARATION
--
-- SOURCE / INTERNAL PROVENANCE
--
-- Hanna Fenichel Pitkin, The Concept of Representation, University of
-- California Press, 1967. Book; no DOI asserted.
--
-- Existing owner: DASHI.Governance.AuthorityMandateCore types authority as a
-- source-scoped, recallable and reviewable relation and explicitly rejects force
-- or elite agreement as self-issuing authority.
--
-- Draft PR #603 independently separates observer refinement, actuation and
-- contested authority.  This thin owner extracts the missing option-cone seam:
-- observing a condition, evaluating it and possessing authority/capacity to
-- modify it are separate proof obligations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- Generic capability interfaces.
------------------------------------------------------------------------

record ConeGovernanceCapabilities
    (Actor State Option : Set)
    (reachability : Cone.SafeReachabilitySystem State Option) : Set₁ where
  constructor cone-governance-capabilities
  field
    CanObserve : Actor → State → Set
    CanEvaluate : Actor → State → Set
    CanModify : Actor → State → Option → Set

open ConeGovernanceCapabilities public

record MandateBackedModification
    {mandate : Authority.Mandate}
    {State Option : Set}
    {reachability : Cone.SafeReachabilitySystem State Option}
    {Actor : Set}
    (capabilities : ConeGovernanceCapabilities Actor State Option reachability)
    (actor : Actor)
    (state : State)
    (option : Option) : Set₁ where
  constructor mandate-backed-modification
  field
    scopedAuthority : Authority.ScopedAuthority mandate
    modificationCapability : CanModify capabilities actor state option

open MandateBackedModification public

------------------------------------------------------------------------
-- Exact finite separation witness.
------------------------------------------------------------------------

data DemoActor : Set where
  observerOnly evaluatorOnly modifierOnly integratedActor : DemoActor

data DemoState : Set where
  closedState openState : DemoState

data DemoOption : Set where
  remainOption : DemoOption

data DemoAvailable : DemoState → DemoOption → Set where
  openRemain : DemoAvailable openState remainOption

demoReachability : Cone.SafeReachabilitySystem DemoState DemoOption
demoReachability = Cone.safeReachabilitySystem DemoAvailable

data DemoCanObserve : DemoActor → DemoState → Set where
  observerSeesClosed : DemoCanObserve observerOnly closedState
  integratedSeesClosed : DemoCanObserve integratedActor closedState

data DemoCanEvaluate : DemoActor → DemoState → Set where
  evaluatorJudgesClosed : DemoCanEvaluate evaluatorOnly closedState
  integratedJudgesClosed : DemoCanEvaluate integratedActor closedState

data DemoCanModify : DemoActor → DemoState → DemoOption → Set where
  modifierCanOpenRemain : DemoCanModify modifierOnly closedState remainOption
  integratedCanOpenRemain : DemoCanModify integratedActor closedState remainOption

demoCapabilities :
  ConeGovernanceCapabilities DemoActor DemoState DemoOption demoReachability
demoCapabilities =
  cone-governance-capabilities DemoCanObserve DemoCanEvaluate DemoCanModify

observerDoesNotAcquireModificationAuthority :
  DemoCanObserve observerOnly closedState →
  DemoCanModify observerOnly closedState remainOption → ⊥
observerDoesNotAcquireModificationAuthority observerSeesClosed ()

evaluatorDoesNotAcquireModificationAuthority :
  DemoCanEvaluate evaluatorOnly closedState →
  DemoCanModify evaluatorOnly closedState remainOption → ⊥
evaluatorDoesNotAcquireModificationAuthority evaluatorJudgesClosed ()

modifierNeedNotHaveInstalledObserver :
  DemoCanModify modifierOnly closedState remainOption →
  DemoCanObserve modifierOnly closedState → ⊥
modifierNeedNotHaveInstalledObserver modifierCanOpenRemain ()

modifierNeedNotHaveInstalledValuation :
  DemoCanModify modifierOnly closedState remainOption →
  DemoCanEvaluate modifierOnly closedState → ⊥
modifierNeedNotHaveInstalledValuation modifierCanOpenRemain ()

integratedActorCarriesAllThree :
  DemoCanObserve integratedActor closedState
  × (DemoCanEvaluate integratedActor closedState
  × DemoCanModify integratedActor closedState remainOption)
integratedActorCarriesAllThree =
  integratedSeesClosed , (integratedJudgesClosed , integratedCanOpenRemain)

record ObserverValuationAuthorityBoundary : Set where
  constructor observer-valuation-authority-boundary
  field
    observationSelfIssuesAuthority : Bool
    observationSelfIssuesAuthorityIsFalse : observationSelfIssuesAuthority ≡ false
    normativeEvaluationSelfIssuesAuthority : Bool
    normativeEvaluationSelfIssuesAuthorityIsFalse :
      normativeEvaluationSelfIssuesAuthority ≡ false
    modificationCapacityImpliesAdequateObserver : Bool
    modificationCapacityImpliesAdequateObserverIsFalse :
      modificationCapacityImpliesAdequateObserver ≡ false
    modificationCapacityImpliesLegitimateMandate : Bool
    modificationCapacityImpliesLegitimateMandateIsFalse :
      modificationCapacityImpliesLegitimateMandate ≡ false
    mandateAloneGuaranteesMaterialRepair : Bool
    mandateAloneGuaranteesMaterialRepairIsFalse :
      mandateAloneGuaranteesMaterialRepair ≡ false

canonicalObserverValuationAuthorityBoundary :
  ObserverValuationAuthorityBoundary
canonicalObserverValuationAuthorityBoundary =
  observer-valuation-authority-boundary
    false refl false refl false refl false refl false refl
