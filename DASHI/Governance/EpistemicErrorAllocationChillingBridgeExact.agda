module DASHI.Governance.EpistemicErrorAllocationChillingBridgeExact where

------------------------------------------------------------------------
-- EPISTEMIC ERROR ALLOCATION / CHILLING BRIDGE
--
-- Small composition layer over InstitutionalNoticeActuationCulpabilityExact
-- and OptionConeCoercionExact.  Failed comprehension can be routed toward
-- repair/refinement or toward fault attribution; a sanction can teach avoidance
-- of the institution without teaching the missing fine distinction.  This is a
-- structural allocation model, not a legal or medical empirical claim.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.InstitutionalNoticeActuationCulpabilityExact as Notice
import DASHI.Governance.OptionConeCoercionExact as OptionCone

------------------------------------------------------------------------
-- 1. Same comprehension failure, different institutional allocation.
------------------------------------------------------------------------

data ComprehensionState : Set where
  unresolvedDecisionFibre : ComprehensionState

data ErrorAllocation : Set where
  repairAsSafetyInformation attributeFaultToSubject : ErrorAllocation

record EpistemicErrorRouting : Set where
  constructor epistemicErrorRouting
  field
    comprehension : ComprehensionState
    allocation : ErrorAllocation

repairRouting : EpistemicErrorRouting
repairRouting = epistemicErrorRouting unresolvedDecisionFibre repairAsSafetyInformation

faultRouting : EpistemicErrorRouting
faultRouting = epistemicErrorRouting unresolvedDecisionFibre attributeFaultToSubject

sameComprehensionDifferentAllocation :
  EpistemicErrorRouting.comprehension repairRouting
    ≡ EpistemicErrorRouting.comprehension faultRouting
sameComprehensionDifferentAllocation = refl

allocationsRemainDistinct :
  EpistemicErrorRouting.allocation repairRouting
    ≡ EpistemicErrorRouting.allocation faultRouting → ⊥
allocationsRemainDistinct ()

record EpistemicErrorAllocationWitness : Set where
  constructor epistemicErrorAllocationWitness
  field
    sameFailureSurface :
      EpistemicErrorRouting.comprehension repairRouting
        ≡ EpistemicErrorRouting.comprehension faultRouting
    allocationNotForcedByFailure :
      EpistemicErrorRouting.allocation repairRouting
        ≡ EpistemicErrorRouting.allocation faultRouting → ⊥

canonicalEpistemicErrorAllocationWitness : EpistemicErrorAllocationWitness
canonicalEpistemicErrorAllocationWitness =
  epistemicErrorAllocationWitness refl (λ ())

------------------------------------------------------------------------
-- 2. Fine-rule learning and institution-avoidance learning are distinct.
------------------------------------------------------------------------

data LearnedOutcome : Set where
  learnedFineDistinction learnedAvoidInstitution : LearnedOutcome

sanctionLearningOutcome : LearnedOutcome
sanctionLearningOutcome = learnedAvoidInstitution

closureLearningOutcome : LearnedOutcome
closureLearningOutcome = learnedFineDistinction

avoidanceIsNotFineRuleLearning :
  sanctionLearningOutcome ≡ closureLearningOutcome → ⊥
avoidanceIsNotFineRuleLearning ()

------------------------------------------------------------------------
-- 3. Chilling has an existing dynamic witness: the canonical option-cone
--    contraction explicitly loses future-help-seeking while another comparison
--    route retains it.
------------------------------------------------------------------------

chillingContractsFutureHelpSeeking :
  OptionCone.StrictSafeReachabilityContraction
    OptionCone.demoReachability
    OptionCone.beforeResponse
    OptionCone.coerciveOutcome
chillingContractsFutureHelpSeeking =
  OptionCone.canonicalCoerciveReachabilityContraction

comparisonRouteRetainsFutureHelpSeeking :
  OptionCone.DemoAvailable OptionCone.communityOutcome OptionCone.futureHelpSeeking
comparisonRouteRetainsFutureHelpSeeking =
  OptionCone.communityRetainsLostCoerciveOption

------------------------------------------------------------------------
-- 4. Repair-before-fault composes with the existing effective-notice boundary.
------------------------------------------------------------------------

repairRouteHasDecisionSafeClosureWitness : Notice.EffectiveNotice Notice.expertObserver
repairRouteHasDecisionSafeClosureWitness =
  Notice.expertRefinementWithClosureIsEffectiveNotice

faultCannotBeDerivedFromDeliveryAtCoarseObserver :
  Notice.DeliveredNotice → Notice.CostsCulpable Notice.layObserver → ⊥
faultCannotBeDerivedFromDeliveryAtCoarseObserver delivered culpable =
  Notice.layPersistenceCannotBePromotedToThisCulpabilityBoundary culpable

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record EpistemicErrorAllocationChillingBoundary : Set where
  constructor epistemicErrorAllocationChillingBoundary
  field
    comprehensionFailureDeterminesFaultAllocation : Bool
    sanctionAutomaticallyTeachesFineRule : Bool
    quietComplianceProvesUnderstanding : Bool
    futureHelpSeekingMayContract : Bool
    repairAndFaultRemainDistinctInstitutionalChoices : Bool

canonicalEpistemicErrorAllocationChillingBoundary :
  EpistemicErrorAllocationChillingBoundary
canonicalEpistemicErrorAllocationChillingBoundary =
  epistemicErrorAllocationChillingBoundary false false false true true
