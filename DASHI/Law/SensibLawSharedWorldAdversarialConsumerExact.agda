module DASHI.Law.SensibLawSharedWorldAdversarialConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SharedUserWorldConsumerRuntimeExact as Shared
import DASHI.Law.SensibLawDialecticalProofSearchExact as Dialectic

------------------------------------------------------------------------
-- SHARED WORLD -> ADVERSARIAL LEGAL CONSUMER
--
-- A legal consumer first asks whether a required coordinate is already
-- legitimately reusable from the shared world.  Reuse may pay a factual or
-- source prerequisite, but legal type, authority, applicability and defeat
-- remain independent gates.
------------------------------------------------------------------------

data LegalAtomRole : Set where
  factAtom : LegalAtomRole
  elementAtom : LegalAtomRole
  ruleAtom : LegalAtomRole
  exceptionAtom : LegalAtomRole
  defeaterAtom : LegalAtomRole
  remedyAtom : LegalAtomRole
  burdenAtom : LegalAtomRole
  authorityAtom : LegalAtomRole
  applicabilityAtom : LegalAtomRole

data LegalSearchDirection : Set where
  forwardProof : LegalSearchDirection
  backwardMissingAtom : LegalSearchDirection
  adversarialDefeater : LegalSearchDirection
  counterAdversarialRepair : LegalSearchDirection
  comparatorSearch : LegalSearchDirection

data LegalRouteState : Set where
  routeReachable : LegalRouteState
  routeDefeated : LegalRouteState
  routeContested : LegalRouteState
  routeUnresolved : LegalRouteState

data SharedWorldLegalReuseOutcome : Set where
  reusableLegalPrerequisite : SharedWorldLegalReuseOutcome
  wrongTypeRequiresResidual : SharedWorldLegalReuseOutcome
  authorityPaymentRequired : SharedWorldLegalReuseOutcome
  legalScopeBlocked : SharedWorldLegalReuseOutcome
  missingSharedCoordinate : SharedWorldLegalReuseOutcome

decideLegalReuse :
  Shared.SharedWorldReuseDisposition ->
  Bool -> -- coordinate has the exact required legal type
  Bool -> -- required authority/applicability payment exists
  SharedWorldLegalReuseOutcome
decideLegalReuse Shared.scopeBlocked _ _ = legalScopeBlocked
decideLegalReuse Shared.researchMissing _ _ = missingSharedCoordinate
decideLegalReuse Shared.reuseAlreadyPaid false _ = wrongTypeRequiresResidual
decideLegalReuse Shared.reuseAlreadyPaid true false = authorityPaymentRequired
decideLegalReuse Shared.reuseAlreadyPaid true true = reusableLegalPrerequisite

record SharedWorldLegalAtomCandidate : Set₁ where
  constructor shared-world-legal-atom-candidate
  field
    lookup : Shared.SharedWorldLookupReceipt
    atomRole : LegalAtomRole
    targetPropositionReference : String
    wrongTypeReference : String
    exactLegalTypeMatched : Bool
    authorityOrApplicabilityPaid : Bool
    outcome : SharedWorldLegalReuseOutcome
    outcomeMatches :
      outcome ≡
      decideLegalReuse
        (Shared.disposition lookup)
        exactLegalTypeMatched
        authorityOrApplicabilityPaid
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    candidateReference : String

open SharedWorldLegalAtomCandidate public

record AdversarialLegalSearchStep : Set where
  constructor adversarial-legal-search-step
  field
    targetPropositionReference : String
    currentRouteState : LegalRouteState
    direction : LegalSearchDirection
    epistemicSearchRole : Dialectic.EpistemicSearchRole
    liveAtomReference : String
    discriminatorReference : String
    stepReference : String
    searchCreatesAuthority : Bool
    searchCreatesAuthorityIsFalse : searchCreatesAuthority ≡ false
    searchCreatesTruth : Bool
    searchCreatesTruthIsFalse : searchCreatesTruth ≡ false

open AdversarialLegalSearchStep public

record AdversarialLegalRerunReceipt : Set where
  constructor adversarial-legal-rerun-receipt
  field
    propositionReference : String
    beforeState : LegalRouteState
    admittedDeltaReference : String
    afterState : LegalRouteState
    nextDirection : LegalSearchDirection
    oldFactsPreserved : Bool
    oldFactsPreservedIsTrue : oldFactsPreserved ≡ true
    rerunReference : String
    routeStatePredictsJudicialOutcome : Bool
    routeStatePredictsJudicialOutcomeIsFalse :
      routeStatePredictsJudicialOutcome ≡ false

open AdversarialLegalRerunReceipt public

------------------------------------------------------------------------
-- Cross-matter reuse is dependency indexed.  It may reuse an already reviewed
-- proposition/source/identity coordinate while leaving each matter's legal
-- issue graph, elements, exceptions and burdens distinct.
------------------------------------------------------------------------

record LegalAffectedConsumerJoin : Set₁ where
  constructor legal-affected-consumer-join
  field
    sharedCoordinate : Shared.SharedWorldCoordinate
    originatingConsumer : Shared.ConsumerDependencySlice
    affectedConsumer : Shared.ConsumerDependencySlice
    dependencyWitnessReference : String
    sharedCoordinateReused : Bool
    sharedCoordinateReusedIsTrue : sharedCoordinateReused ≡ true
    issueGraphsCollapsed : Bool
    issueGraphsCollapsedIsFalse : issueGraphsCollapsed ≡ false
    joinReference : String

open LegalAffectedConsumerJoin public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReviewedJournalEventAutomaticallyLegalEvidence : Set where
data SharedCoordinateAutomaticallyPaysLegalAtom : Set where
data AnalogyAutomaticallyCreatesAuthorityPayment : Set where
data ReachableRoutePredictsJudicialOutcome : Set where
data DefeatedRouteMeansPropositionFalse : Set where
data CounterDefeaterCandidateIsCurrentLaw : Set where
data CrossMatterJoinCollapsesIssueGraphs : Set where

journalReviewDoesNotAutoCreateLegalEvidence :
  ReviewedJournalEventAutomaticallyLegalEvidence -> ⊥
journalReviewDoesNotAutoCreateLegalEvidence ()

sharedCoordinateDoesNotAutoPayLegalAtom :
  SharedCoordinateAutomaticallyPaysLegalAtom -> ⊥
sharedCoordinateDoesNotAutoPayLegalAtom ()

analogyDoesNotCreateAuthorityPayment :
  AnalogyAutomaticallyCreatesAuthorityPayment -> ⊥
analogyDoesNotCreateAuthorityPayment ()

reachableDoesNotPredictJudicialOutcome :
  ReachableRoutePredictsJudicialOutcome -> ⊥
reachableDoesNotPredictJudicialOutcome ()

defeatDoesNotMeanFalsity :
  DefeatedRouteMeansPropositionFalse -> ⊥
defeatDoesNotMeanFalsity ()

repairCandidateDoesNotBecomeLaw :
  CounterDefeaterCandidateIsCurrentLaw -> ⊥
repairCandidateDoesNotBecomeLaw ()

joinDoesNotCollapseIssues :
  CrossMatterJoinCollapsesIssueGraphs -> ⊥
joinDoesNotCollapseIssues ()

record SharedWorldAdversarialLegalBoundary : Set where
  constructor shared-world-adversarial-legal-boundary
  field
    sharedWorldLookupComesBeforeLegalAcquisition : Bool
    sharedWorldLookupComesBeforeLegalAcquisitionIsTrue :
      sharedWorldLookupComesBeforeLegalAcquisition ≡ true
    supportAndDefeaterSearchRemainFirstClass : Bool
    supportAndDefeaterSearchRemainFirstClassIsTrue :
      supportAndDefeaterSearchRemainFirstClass ≡ true
    counterDefeaterSearchMayReopenRoute : Bool
    counterDefeaterSearchMayReopenRouteIsTrue :
      counterDefeaterSearchMayReopenRoute ≡ true
    wrongTypeRoutesToMissingAtom : Bool
    wrongTypeRoutesToMissingAtomIsTrue :
      wrongTypeRoutesToMissingAtom ≡ true
    routeReachabilityEqualsJudicialPrediction : Bool
    routeReachabilityEqualsJudicialPredictionIsFalse :
      routeReachabilityEqualsJudicialPrediction ≡ false

canonicalSharedWorldAdversarialLegalBoundary :
  SharedWorldAdversarialLegalBoundary
canonicalSharedWorldAdversarialLegalBoundary =
  shared-world-adversarial-legal-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
