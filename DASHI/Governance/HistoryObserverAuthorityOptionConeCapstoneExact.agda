module DASHI.Governance.HistoryObserverAuthorityOptionConeCapstoneExact where

------------------------------------------------------------------------
-- HISTORY / ECOLOGY / OBSERVER / AUTHORITY OPTION-CONE CAPSTONE
--
-- This is the regression root for the highest-alpha cross-pollination among
-- draft PRs #606, #618, #620 and #603.  It imports only owners available on the
-- current ancestry; adjacent draft branches remain theorem-pattern provenance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverAffordanceIncomparabilityExact as Incomparable
import DASHI.Core.RelationalityGradeSeparationExact as Grades
import DASHI.Governance.HistoryConditionedSocialEcologyOptionConeExact as HistoryEcology
import DASHI.Governance.ObserverValuationAuthoritySeparationExact as Authority
import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- Observer and realized affordance are incomparable in both directions.
------------------------------------------------------------------------

observerCannotRecoverAffordance :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Incomparable.squareObservation Incomparable.squareAffordance → ⊥
observerCannotRecoverAffordance =
  Incomparable.observationDoesNotDetermineAffordance
    Incomparable.canonicalObserverAffordanceIncomparability

affordanceCannotRecoverObserver :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Incomparable.squareAffordance Incomparable.squareObservation → ⊥
affordanceCannotRecoverObserver =
  Incomparable.affordanceDoesNotDetermineObservation
    Incomparable.canonicalObserverAffordanceIncomparability

------------------------------------------------------------------------
-- Independent history/ecology contractions stay live as proof-bearing cones.
------------------------------------------------------------------------

historyCanContractAtFixedEcology :
  Cone.StrictSafeReachabilityContraction
    HistoryEcology.socialReachability
    HistoryEcology.regulatedSupportive
    HistoryEcology.mobilisedSupportive
historyCanContractAtFixedEcology = HistoryEcology.historyConditionedContraction

ecologyCanContractAtFixedHistory :
  Cone.StrictSafeReachabilityContraction
    HistoryEcology.socialReachability
    HistoryEcology.regulatedSupportive
    HistoryEcology.regulatedHostile
ecologyCanContractAtFixedHistory = HistoryEcology.ecologyConditionedContraction

jointConditionCanContractFurther :
  Cone.StrictSafeReachabilityContraction
    HistoryEcology.socialReachability
    HistoryEcology.regulatedSupportive
    HistoryEcology.mobilisedHostile
jointConditionCanContractFurther = HistoryEcology.jointHistoryEcologyContraction

------------------------------------------------------------------------
-- Observation, valuation and modification capacity remain separate.
------------------------------------------------------------------------

seeingDoesNotIssueModification :
  Authority.DemoCanObserve Authority.observerOnly Authority.closedState →
  Authority.DemoCanModify Authority.observerOnly Authority.closedState
    Authority.remainOption → ⊥
seeingDoesNotIssueModification =
  Authority.observerDoesNotAcquireModificationAuthority

valuingDoesNotIssueModification :
  Authority.DemoCanEvaluate Authority.evaluatorOnly Authority.closedState →
  Authority.DemoCanModify Authority.evaluatorOnly Authority.closedState
    Authority.remainOption → ⊥
valuingDoesNotIssueModification =
  Authority.evaluatorDoesNotAcquireModificationAuthority

------------------------------------------------------------------------
-- Relationality grades remain proof obligations, not automatic promotions.
------------------------------------------------------------------------

pairValuedIsNotYetNonseparable :
  Grades.requiresNonseparabilityWitness Grades.pairValued ≡ false
pairValuedIsNotYetNonseparable = Grades.pairValuedDoesNotRequireNonseparability

historyIsNotYetObserverConditioning :
  Grades.requiresObserverOrContextCoordinate Grades.historyConditioned ≡ false
historyIsNotYetObserverConditioning =
  Grades.historyConditionedDoesNotRequireObserverContext

record HistoryObserverAuthorityCapstoneBoundary : Set where
  constructor history-observer-authority-capstone-boundary
  field
    stateEqualsRelation : Bool
    stateEqualsRelationIsFalse : stateEqualsRelation ≡ false
    relationEqualsHistory : Bool
    relationEqualsHistoryIsFalse : relationEqualsHistory ≡ false
    historyEqualsReachablePossibility : Bool
    historyEqualsReachablePossibilityIsFalse :
      historyEqualsReachablePossibility ≡ false
    reachablePossibilityEqualsObserver : Bool
    reachablePossibilityEqualsObserverIsFalse :
      reachablePossibilityEqualsObserver ≡ false
    observerEqualsValuation : Bool
    observerEqualsValuationIsFalse : observerEqualsValuation ≡ false
    valuationEqualsAuthority : Bool
    valuationEqualsAuthorityIsFalse : valuationEqualsAuthority ≡ false
    authorityGuaranteesRepair : Bool
    authorityGuaranteesRepairIsFalse : authorityGuaranteesRepair ≡ false

canonicalHistoryObserverAuthorityCapstoneBoundary :
  HistoryObserverAuthorityCapstoneBoundary
canonicalHistoryObserverAuthorityCapstoneBoundary =
  history-observer-authority-capstone-boundary
    false refl false refl false refl false refl false refl false refl false refl
