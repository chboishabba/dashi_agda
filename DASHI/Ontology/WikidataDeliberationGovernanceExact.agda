module DASHI.Ontology.WikidataDeliberationGovernanceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.EpistemicInquiryGovernance as Governance
import DASHI.Ontology.WikidataDiagnosticGovernanceExact as Diagnostic

------------------------------------------------------------------------
-- Source attribution and exact boundary (2026-11-01)
--
-- Marcin Roszkowski, "Navigating change: an exploration of socio-epistemic
-- process of extending Wikidata ontology with new properties",
-- Journal of Documentation 80(6), 1291-1312 (2024).
-- DOI: 10.1108/JD-01-2024-0008.
-- Wikimedia CEE conference presentation (2026):
-- "Done. Make Good Use of It." Epistemic Practices Behind Wikidata's
-- Ontology Evolution.
--
-- Roszkowski motivates the distinction between initiation, knowledge work
-- and closure. The predicates/records/projections and conditional theorems
-- below are *DASHI-local*, not results asserted by Roszkowski.
--
-- Reuses the existing DASHI EpistemicInquiryGovernance and
-- WikidataDiagnosticGovernanceExact owners; does not model consensus by a
-- numeric vote and does not elevate an edit or community decision receipt
-- into a proposition about biological/ontological world truth.
------------------------------------------------------------------------

data DeliberationPhase : Set where
  initiation : DeliberationPhase
  knowledgeWork : DeliberationPhase
  closure : DeliberationPhase

data SourceEventKind : Set where
  proposalEvent : SourceEventKind
  supportEvent : SourceEventKind
  objectionEvent : SourceEventKind
  amendmentEvent : SourceEventKind
  decisionEvent : SourceEventKind

-- A revision/byte range/hash *claim* is inspectable data, not automatically
-- a cryptographic, temporal or semantic authentication witness.
record SourceAnchoredEvent : Set where
  constructor sourceAnchoredEvent
  field
    sourceRevisionRef : String
    startByte : Nat
    endByte : Nat
    excerptDigestRef : String
    actorRef : String
    eventKind : SourceEventKind
    observedAtEpochSeconds : Nat

open SourceAnchoredEvent public

-- The independent source reopener may supply an authenticated witness after
-- actually checking canonical source bytes; a bare ref cannot inhabit it.
record SourceVerifier : Set₁ where
  constructor sourceVerifier
  field
    Authenticated : SourceAnchoredEvent → Set
    PolicyAuthenticated : String → Set

open SourceVerifier public

-- Historical property-creation policy is supplied explicitly. The actor's
-- admissibility, consensus, effective-policy evidence and age condition are
-- separate predicates; none is computed from a count of approving comments.
record CommunityRule (Agent : Set) : Set₁ where
  constructor communityRule
  field
    CreatorAuthorised : Agent → Set
    IndependentCreator : Agent → SourceAnchoredEvent → Set
    ConsensusWitnessed : String → Set
    PolicyVersionValid : String → Set
    RequiredAgeSatisfied : Nat → Nat → Set

open CommunityRule public

record DeliberationCase : Set where
  constructor deliberationCase
  field
    proposal : SourceAnchoredEvent
    closingDecision : SourceAnchoredEvent
    historicalPolicyRef : String
    proposalRef : String

open DeliberationCase public

record ClosureAdmission
    {Agent : Set}
    (verifier : SourceVerifier)
    (rule : CommunityRule Agent)
    (creator : Agent)
    (caseFile : DeliberationCase) : Set₁ where
  constructor closureAdmission
  field
    proposalAuthenticated : Authenticated verifier (proposal caseFile)
    decisionAuthenticated : Authenticated verifier (closingDecision caseFile)
    policySourceAuthenticated :
      PolicyAuthenticated verifier (historicalPolicyRef caseFile)
    creatorAuthority : CreatorAuthorised rule creator
    creatorDistinctFromProposer :
      IndependentCreator rule creator (proposal caseFile)
    deliberativeConsensus : ConsensusWitnessed rule (proposalRef caseFile)
    historicalPolicyApplicable :
      PolicyVersionValid rule (historicalPolicyRef caseFile)
    policyTimeGuard :
      RequiredAgeSatisfied rule
        (observedAtEpochSeconds (proposal caseFile))
        (observedAtEpochSeconds (closingDecision caseFile))

open ClosureAdmission public

-- The following are genuine projection results, conditional on *all*
-- external witnesses. They make each required field a separately actionable
-- missing-evidence obligation for an SLR/ITIR producer.
admissionRequiresCreatorAuthority :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  ClosureAdmission verifier rule creator caseFile →
  CreatorAuthorised rule creator
admissionRequiresCreatorAuthority admission =
  creatorAuthority admission

admissionRequiresIndependentCreator :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  ClosureAdmission verifier rule creator caseFile →
  IndependentCreator rule creator (proposal caseFile)
admissionRequiresIndependentCreator admission =
  creatorDistinctFromProposer admission

admissionRequiresPolicySource :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  ClosureAdmission verifier rule creator caseFile →
  PolicyAuthenticated verifier (historicalPolicyRef caseFile)
admissionRequiresPolicySource admission =
  policySourceAuthenticated admission

admissionRequiresConsensus :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  ClosureAdmission verifier rule creator caseFile →
  ConsensusWitnessed rule (proposalRef caseFile)
admissionRequiresConsensus admission =
  deliberativeConsensus admission

admissionRequiresPolicyVersion :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  ClosureAdmission verifier rule creator caseFile →
  PolicyVersionValid rule (historicalPolicyRef caseFile)
admissionRequiresPolicyVersion admission =
  historicalPolicyApplicable admission

admissionRequiresExactSource :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  ClosureAdmission verifier rule creator caseFile →
  Authenticated verifier (proposal caseFile)
admissionRequiresExactSource admission =
  proposalAuthenticated admission

noCreatorAuthorityBlocksClosure :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  (CreatorAuthorised rule creator → ⊥) →
  ClosureAdmission verifier rule creator caseFile → ⊥
noCreatorAuthorityBlocksClosure noAuthority admitted =
  noAuthority (creatorAuthority admitted)

sameActorCreatorBlocksClosure :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  (IndependentCreator rule creator (proposal caseFile) → ⊥) →
  ClosureAdmission verifier rule creator caseFile → ⊥
sameActorCreatorBlocksClosure notIndependent admitted =
  notIndependent (creatorDistinctFromProposer admitted)

missingPolicySourceBlocksClosure :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  (PolicyAuthenticated verifier (historicalPolicyRef caseFile) → ⊥) →
  ClosureAdmission verifier rule creator caseFile → ⊥
missingPolicySourceBlocksClosure noWitness admitted =
  noWitness (policySourceAuthenticated admitted)

missingConsensusBlocksClosure :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  (ConsensusWitnessed rule (proposalRef caseFile) → ⊥) →
  ClosureAdmission verifier rule creator caseFile → ⊥
missingConsensusBlocksClosure noConsensus admitted =
  noConsensus (deliberativeConsensus admitted)

missingSourceAuthenticationBlocksClosure :
  ∀ {Agent : Set}
    {verifier : SourceVerifier}
    {rule : CommunityRule Agent}
    {creator : Agent}
    {caseFile : DeliberationCase} →
  (Authenticated verifier (proposal caseFile) → ⊥) →
  ClosureAdmission verifier rule creator caseFile → ⊥
missingSourceAuthenticationBlocksClosure noWitness admitted =
  noWitness (proposalAuthenticated admitted)

-- Positive support and counter-support are independently retained. An
-- approving discussion and a contrary argument can coexist without logical
-- explosion or truth promotion.
record DeliberationContestationFibre : Set where
  constructor deliberationContestationFibre
  field
    supportObserved : Bool
    counterSupportObserved : Bool

open DeliberationContestationFibre public

bothObserved : DeliberationContestationFibre
bothObserved = deliberationContestationFibre true true

neitherObserved : DeliberationContestationFibre
neitherObserved = deliberationContestationFibre false false

-- A diagnostic checker has no built-in target-ontology revision authority.
-- Reuse the original theorem owner rather than constructing a second rule.
formalCheckerDoesNotSelfAuthoriseCommunityRevision :
  Diagnostic.DiagnosticAuthorises
    Diagnostic.formalChecker Governance.revisionCoordinate → ⊥
formalCheckerDoesNotSelfAuthoriseCommunityRevision =
  Diagnostic.formalCheckerCannotSelfAuthoriseRevision

-- Only an independently authenticated community rule may provide a closure
-- admission. Even an admitted closure is a policy/decision record, never an
-- automatic edit action or a proof of statement truth.
data AutomaticExternalEditPermission : Set where

sourceEvidenceDoesNotGrantAutomaticExternalEdit :
  (event : SourceAnchoredEvent) →
  AutomaticExternalEditPermission → ⊥
sourceEvidenceDoesNotGrantAutomaticExternalEdit event ()

record DeliberationGovernanceBoundary : Set where
  constructor deliberationGovernanceBoundary
  field
    sourceReferenceAloneAuthenticates : Bool
    creatorAuthorityFollowsFromParticipation : Bool
    consensusFollowsFromSupportCount : Bool
    policyVersionIsTimeIndexed : Bool
    closureImpliesWikidataEdit : Bool

canonicalDeliberationGovernanceBoundary : DeliberationGovernanceBoundary
canonicalDeliberationGovernanceBoundary =
  deliberationGovernanceBoundary false false false true false
