module DASHI.Education.SituatedRelationalLearningAffordanceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.ConsentAgencyGovernanceCore as Consent
import DASHI.Biology.EcologyOfDataHyperfabricBridge as Ecology
import DASHI.Biology.EvolvedSensoryTransport as Sensory
import DASHI.Biology.Levin.NicheConstructionProblemSpace as Niche
import DASHI.Biology.PsychogeographicFieldExact as Psychogeography
import DASHI.ChildAuthorityTraumaHyperfabric as ChildAuthority
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as TraumaMemory
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Education.DevelopmentalAffordanceAttunementExact as Affordance
import DASHI.Education.EarlyLearningComparativeArchitectureExact as Comparative
import DASHI.Education.EarlyLearningComparativeEvidenceSourceRegistry as ComparativeSources
import DASHI.Education.RoseContextLearningSourceBoundary as Rose
import DASHI.Governance.AutonomyReopeningCriterion as Reopening
import DASHI.Governance.DevelopmentalAgencyState as Agency
import DASHI.Philosophy.PatternPreservingTeaching as PatternTeaching
import DASHI.Reasoning.DevelopmentalAttunementPNFBridge as Attunement

------------------------------------------------------------------------
-- SITUATED RELATIONAL LEARNING AFFORDANCE
--
-- The repo-wide cross-pollination closes a remaining compression error:
--
--   available != reachable != contestable/agentic.
--
-- An activity, curriculum resource, teacher, place or sensory opportunity may
-- be nominally present while remaining inaccessible, dysregulating, temporally
-- mismatched, socially unavailable, or impossible for the child to decline or
-- reshape.  Conversely, temporary structure need not destroy autonomy if it
-- preserves/reforges access to reasons, alternatives, refusal and later
-- revision.  The formal carrier therefore keeps reachability, contestability,
-- history and measurement horizon separate from availability.
------------------------------------------------------------------------

data ReachabilityState : Set where
  unavailable availableButBlocked reachable : ReachabilityState

data ContestabilityState : Set where
  adultDirectedOnly acceptOrDecline acceptDeclineOrModify : ContestabilityState

data DevelopmentalMeasurementHorizon : Set where
  immediateSnapshot intermediateHorizon longitudinalHorizon : DevelopmentalMeasurementHorizon

data HistoricalAccessibility : Set where
  historyUnspecified historyBarrierRetained historyRevisionRouteRetained : HistoricalAccessibility

reachabilityBool : ReachabilityState → Bool
reachabilityBool unavailable = false
reachabilityBool availableButBlocked = false
reachabilityBool reachable = true

contestabilityBool : ContestabilityState → Bool
contestabilityBool adultDirectedOnly = false
contestabilityBool acceptOrDecline = true
contestabilityBool acceptDeclineOrModify = true

record SituatedRelationalLearningAffordance : Set where
  constructor situatedRelationalLearningAffordance
  field
    nominallyAvailable : Bool
    reachability : ReachabilityState
    contestability : ContestabilityState
    developmentalPhase : Affordance.DevelopmentalPhase
    temporalOrganisation : Affordance.TemporalOrganisation
    childPreferenceVisibility : Affordance.ChildPreferenceVisibility
    safeMediationPresent : Bool
    structuredScaffoldingPresent : Bool
    relationalReviewPresent : Bool
    placeAndRouteHistoryRetained : Bool
    sensoryContextRetained : Bool
    developmentalHistoryRetained : Bool
    historicalAccessibility : HistoricalAccessibility
    measurementHorizon : DevelopmentalMeasurementHorizon
    publicEntitlementRetained : Bool
    localLifeworldRetained : Bool
    receipt : String

open SituatedRelationalLearningAffordance public

------------------------------------------------------------------------
-- Exact finite falsifier 1: nominal availability cannot determine whether the
-- opportunity is actually reachable.
------------------------------------------------------------------------

availableBlockedAffordance : SituatedRelationalLearningAffordance
availableBlockedAffordance =
  situatedRelationalLearningAffordance
    true availableButBlocked adultDirectedOnly
    Affordance.earlyExploration Affordance.fragmentedTiming
    Affordance.preferenceOccluded
    false true false true true true historyBarrierRetained
    immediateSnapshot true true
    "resource/activity is nominally present, but the child cannot currently reach it through the retained relational/contextual topology"

availableReachableAffordance : SituatedRelationalLearningAffordance
availableReachableAffordance =
  situatedRelationalLearningAffordance
    true reachable acceptDeclineOrModify
    Affordance.earlyExploration Affordance.contingentPredictableTiming
    Affordance.preferenceContestableVisible
    true true true true true true historyRevisionRouteRetained
    longitudinalHorizon true true
    "same nominal availability, with a reachable, reviewable and contestable route through the learning ecology"

availabilityProjection : SituatedRelationalLearningAffordance → Bool
availabilityProjection = nominallyAvailable

reachabilityWitness : SituatedRelationalLearningAffordance → Bool
reachabilityWitness affordance = reachabilityBool (reachability affordance)

sameAvailability :
  availabilityProjection availableBlockedAffordance ≡
  availabilityProjection availableReachableAffordance
sameAvailability = refl

sameAvailabilityDifferentReachability :
  reachabilityWitness availableBlockedAffordance ≡
  reachabilityWitness availableReachableAffordance → ⊥
sameAvailabilityDifferentReachability ()

availabilityReachabilityNonFactorability :
  Intersection.NonFactorabilityWitness availabilityProjection reachabilityWitness
availabilityReachabilityNonFactorability =
  Intersection.nonFactorabilityWitness
    availableBlockedAffordance availableReachableAffordance
    sameAvailability sameAvailabilityDifferentReachability

availableAffordanceCannotDetermineReachability :
  Intersection.FactorsThrough availabilityProjection reachabilityWitness → ⊥
availableAffordanceCannotDetermineReachability =
  Intersection.witnessRulesOutEveryFlatFactorisation
    availabilityReachabilityNonFactorability

------------------------------------------------------------------------
-- Exact finite falsifier 2: reachability itself still does not determine
-- developmental agency.  A reachable adult-directed activity and a reachable
-- child-contestable activity share the same reachability projection.
------------------------------------------------------------------------

reachableAdultDirectedAffordance : SituatedRelationalLearningAffordance
reachableAdultDirectedAffordance =
  situatedRelationalLearningAffordance
    true reachable adultDirectedOnly
    Affordance.emergingSymbolic Affordance.contingentPredictableTiming
    Affordance.preferenceOccluded
    true true true true true true historyRevisionRouteRetained
    intermediateHorizon true true
    "reachable activity whose adult-defined route does not itself establish child contestability"

reachableContestableAffordance : SituatedRelationalLearningAffordance
reachableContestableAffordance =
  situatedRelationalLearningAffordance
    true reachable acceptDeclineOrModify
    Affordance.emergingSymbolic Affordance.contingentPredictableTiming
    Affordance.preferenceContestableVisible
    true true true true true true historyRevisionRouteRetained
    intermediateHorizon true true
    "reachable activity with a retained child route to accept, decline or modify participation"

reachableProjection : SituatedRelationalLearningAffordance → Bool
reachableProjection = reachabilityWitness

contestableAgencyWitness : SituatedRelationalLearningAffordance → Bool
contestableAgencyWitness affordance = contestabilityBool (contestability affordance)

sameReachability :
  reachableProjection reachableAdultDirectedAffordance ≡
  reachableProjection reachableContestableAffordance
sameReachability = refl

sameReachabilityDifferentContestability :
  contestableAgencyWitness reachableAdultDirectedAffordance ≡
  contestableAgencyWitness reachableContestableAffordance → ⊥
sameReachabilityDifferentContestability ()

reachabilityAgencyNonFactorability :
  Intersection.NonFactorabilityWitness reachableProjection contestableAgencyWitness
reachabilityAgencyNonFactorability =
  Intersection.nonFactorabilityWitness
    reachableAdultDirectedAffordance reachableContestableAffordance
    sameReachability sameReachabilityDifferentContestability

reachabilityCannotDetermineDevelopmentalAgency :
  Intersection.FactorsThrough reachableProjection contestableAgencyWitness → ⊥
reachabilityCannotDetermineDevelopmentalAgency =
  Intersection.witnessRulesOutEveryFlatFactorisation
    reachabilityAgencyNonFactorability

------------------------------------------------------------------------
-- Exact reuse of the missing child-agency/autonomy lanes.
--
-- Developmental agency is capability- and domain-relative.  Guardian
-- permission is not child competence; assent is not mature consent; refusal
-- and withdrawal remain distinct.  Temporary scaffolding is not automatically
-- indoctrination, because later reopening of reasons/alternatives/revision is a
-- separate developmental coordinate.
------------------------------------------------------------------------

canonicalConsentGovernance : Consent.ConsentAgencyGovernance
canonicalConsentGovernance = Consent.canonicalConsentAgencyGovernance

canonicalDevelopmentalConsentBoundary : Agency.DevelopmentalConsentBoundary
canonicalDevelopmentalConsentBoundary = Agency.canonicalDevelopmentalConsentBoundary

canonicalAutonomyReopeningBoundary : Reopening.AutonomyReopeningBoundary
canonicalAutonomyReopeningBoundary = Reopening.canonicalAutonomyReopeningBoundary

refusalIsRetainedInCanonicalGovernance :
  Consent.refusalPreserved canonicalConsentGovernance ≡ true
refusalIsRetainedInCanonicalGovernance = refl

withdrawalIsRetainedInCanonicalGovernance :
  Consent.withdrawalPreserved canonicalConsentGovernance ≡ true
withdrawalIsRetainedInCanonicalGovernance = refl

guardianPermissionStillDoesNotEqualChildCompetence :
  Agency.guardianPermissionEqualsChildCompetence canonicalDevelopmentalConsentBoundary ≡ false
guardianPermissionStillDoesNotEqualChildCompetence = refl

temporaryScaffoldingStillDoesNotEqualIndoctrination :
  Reopening.temporaryScaffoldingAloneIsIndoctrination canonicalAutonomyReopeningBoundary ≡ false
temporaryScaffoldingStillDoesNotEqualIndoctrination = refl

------------------------------------------------------------------------
-- Trauma/history is retained as a reachability coordinate without promotion
-- to diagnosis or deterministic developmental outcome.
------------------------------------------------------------------------

canonicalTraumaMemoryBoundary : TraumaMemory.TraumaMemoryHypervoxelAuthorityBoundary
canonicalTraumaMemoryBoundary =
  TraumaMemory.canonicalTraumaMemoryHypervoxelAuthorityBoundary

canonicalChildAuthorityHyperformalism : ChildAuthority.ChildAuthorityTraumaHyperfabric
canonicalChildAuthorityHyperformalism =
  ChildAuthority.canonicalChildAuthorityTraumaHyperfabric

traumaResidualStillDoesNotProveTrauma :
  TraumaMemory.residualAloneProvesTrauma canonicalTraumaMemoryBoundary ≡ false
traumaResidualStillDoesNotProveTrauma = refl

formalMemoryCarrierStillDoesNotDiagnosePerson :
  TraumaMemory.formalCarrierDiagnosesPerson canonicalTraumaMemoryBoundary ≡ false
formalMemoryCarrierStillDoesNotDiagnosePerson = refl

complianceStillDoesNotPromoteToConsent :
  ChildAuthority.complianceConsentPromotion canonicalChildAuthorityHyperformalism ≡ false
complianceStillDoesNotPromoteToConsent = refl

scalarCapacityStillNotSufficient :
  ChildAuthority.scalarCapacitySufficientPromotion canonicalChildAuthorityHyperformalism ≡ false
scalarCapacityStillNotSufficient = refl

------------------------------------------------------------------------
-- Place, sensory context, laminated teaching and niche construction are reused
-- without carrier collapse.
------------------------------------------------------------------------

canonicalEcology : Ecology.EcologyOfDataHyperfabricBridge
canonicalEcology = Ecology.canonicalEcologyOfDataHyperfabricBridge

canonicalRoseBoundary : Rose.RoseContextEvidenceBoundary
canonicalRoseBoundary = Rose.canonicalRoseContextEvidenceBoundary

canonicalPatternTeachingBoundary : PatternTeaching.TeachingBoundary
canonicalPatternTeachingBoundary = PatternTeaching.canonicalTeachingBoundary

canonicalPsychogeographicBoundary : Psychogeography.PsychogeographicFieldBoundary
canonicalPsychogeographicBoundary = Psychogeography.canonicalPsychogeographicFieldBoundary

canonicalNicheConstructionBoundary : Niche.NicheConstructionBoundary
canonicalNicheConstructionBoundary = Niche.canonicalNicheConstructionBoundary

roseExposureStillDoesNotEstablishLearningBenefit :
  Rose.exposureAloneProvesUniversalLearningBenefit canonicalRoseBoundary ≡ false
roseExposureStillDoesNotEstablishLearningBenefit = refl

sameEndpointStillDoesNotDetermineLivedAffordance :
  Psychogeography.endpointDeterminesLivedResult canonicalPsychogeographicBoundary ≡ false
sameEndpointStillDoesNotDetermineLivedAffordance = refl

futureAffordanceChangeStillNeedsLongitudinalWitness :
  Niche.futureAffordanceChangeRequiresLongitudinalWitness
    canonicalNicheConstructionBoundary ≡ true
futureAffordanceChangeStillNeedsLongitudinalWitness = refl

------------------------------------------------------------------------
-- Waldorf/Steiner contributes only a source-bounded measurement-horizon
-- warning here.  The repo has comparative evidence metadata, not a canonical
-- Steiner ontology.  We therefore retain the empirical source without
-- promoting its school-level trajectory into a causal pedagogical theorem.
------------------------------------------------------------------------

waldorfMeasurementHorizonSource : ComparativeSources.ComparativeReference
waldorfMeasurementHorizonSource = ComparativeSources.telferRadzat2024

------------------------------------------------------------------------
-- No scalar promotion at the new boundary.
------------------------------------------------------------------------

data AvailabilityEqualsReachabilityPermission : Set where
data ReachabilityEqualsAgencyPermission : Set where
data AdultOfferEqualsChildAssentPermission : Set where
data EarlySnapshotEqualsDevelopmentalTrajectoryPermission : Set where
data HistoryDeterminesDiagnosisPermission : Set where
data AffordanceExpansionAlwaysGoodPermission : Set where

availabilityCannotAutoPromoteToReachability :
  AvailabilityEqualsReachabilityPermission → ⊥
availabilityCannotAutoPromoteToReachability ()

reachabilityCannotAutoPromoteToAgency :
  ReachabilityEqualsAgencyPermission → ⊥
reachabilityCannotAutoPromoteToAgency ()

adultOfferCannotAutoPromoteToChildAssent :
  AdultOfferEqualsChildAssentPermission → ⊥
adultOfferCannotAutoPromoteToChildAssent ()

earlySnapshotCannotAutoPromoteToFullTrajectory :
  EarlySnapshotEqualsDevelopmentalTrajectoryPermission → ⊥
earlySnapshotCannotAutoPromoteToFullTrajectory ()

historyCannotAutoPromoteToDiagnosis : HistoryDeterminesDiagnosisPermission → ⊥
historyCannotAutoPromoteToDiagnosis ()

affordanceExpansionCannotAutoPromoteToBenefit :
  AffordanceExpansionAlwaysGoodPermission → ⊥
affordanceExpansionCannotAutoPromoteToBenefit ()

------------------------------------------------------------------------
-- A positive design gate.  This does not prove a child outcome.  It specifies
-- the dimensions that must travel together before a policy may describe an
-- offered opportunity as a reachable, contestable developmental affordance.
------------------------------------------------------------------------

record ReachableContestableAffordanceGate : Set where
  constructor reachableContestableAffordanceGate
  field
    nominalAvailabilityRetained : Bool
    actualReachabilityRetained : Bool
    childAcceptDeclineModifyRouteRetained : Bool
    refusalAndWithdrawalRetained : Bool
    safeMediationRetained : Bool
    structuredScaffoldingCanCoexistWithAutonomy : Bool
    relationalReviewRetained : Bool
    placeAndSensoryContextRetained : Bool
    developmentalHistoryRetained : Bool
    measurementHorizonDeclared : Bool
    publicEntitlementRetained : Bool
    longitudinalEvidenceRequiredForFutureExpansionClaim : Bool

open ReachableContestableAffordanceGate public

canonicalReachableContestableAffordanceGate : ReachableContestableAffordanceGate
canonicalReachableContestableAffordanceGate =
  reachableContestableAffordanceGate
    true true true true true true true true true true true true

------------------------------------------------------------------------
-- Existing comparative/attunement results remain upstream: the new theorem is
-- a refinement, not a replacement.
------------------------------------------------------------------------

professionalFloorStillCannotDetermineOutcome =
  Comparative.professionalFloorCannotDetermineOutcome

homeDeliveryStillCannotDetermineOutcome =
  Comparative.homeDeliveryCannotDetermineAcademicOutcome

attentionQuantityStillCannotDetermineAttunement =
  Affordance.attentionQuantityCannotDetermineAttunementBurden

affordanceInventoryStillCannotDetermineFit =
  Affordance.affordanceInventoryCannotDetermineDevelopmentalFit

situatedRelationalLearningAffordanceReading : String
situatedRelationalLearningAffordanceReading =
  "The policy-relevant developmental object is not the route, resource inventory, professional presence or nominal affordance count. Availability may fail to be reachable; reachability may fail to be contestable; temporary structure may preserve later autonomy; developmental history may alter accessibility without diagnosing the child; and early measurements do not exhaust a trajectory. Preserve public entitlement while governing reachable, safely mediated and contestable affordances through plural relational authority, declared developmental horizons and evidence-return loops."
