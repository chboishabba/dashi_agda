module DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.SensibLawUnifiedPNFIntakeReentrySpineExact as Intake

------------------------------------------------------------------------
-- M12.2 persistent/traversable source -> statement -> observation -> event.
--
-- This owner is intentionally storage-shape agnostic.  It owns the semantic
-- invariants that the production PostgreSQL rows must preserve.
------------------------------------------------------------------------

record PersistentStatementIdentity : Set where
  constructor persistent-statement-identity
  field
    statementRef : String
    documentRef : String
    sourceRevisionRef : String
    exactSpanRef : String
    literalText : String

open PersistentStatementIdentity public

record ParserRunIdentity : Set where
  constructor parser-run-identity
  field
    parserRunRef : String
    parserProfileRef : String

open ParserRunIdentity public

data StatementIdentityIsParserRunIdentity : Set where

statementIdentityDoesNotCollapseToParserRun :
  StatementIdentityIsParserRunIdentity → ⊥
statementIdentityDoesNotCollapseToParserRun ()

record StatementCandidateObservationLink : Set where
  constructor statement-candidate-observation-link
  field
    statement : PersistentStatementIdentity
    candidatePNFRef : String
    observationRef : String
    parserRun : ParserRunIdentity
    parseReviewRef : String
    semanticAdmissionReceiptRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open StatementCandidateObservationLink public

record ObservationEventLink : Set where
  constructor observation-event-link
  field
    observationRef : String
    eventRef : String
    assemblyReceiptRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false

open ObservationEventLink public

record SemanticTracePath : Set where
  constructor semantic-trace-path
  field
    statement : PersistentStatementIdentity
    candidatePNFRef : String
    parseReviewRef : String
    semanticAdmissionReceiptRef : String
    observationRef : String
    eventRef : String
    claimRefs : List String
    downstreamUseRefs : List String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open SemanticTracePath public

traceFromLinks :
  StatementCandidateObservationLink →
  ObservationEventLink →
  List String →
  List String →
  SemanticTracePath
traceFromLinks statementLink eventLink claims downstream =
  semantic-trace-path
    (StatementCandidateObservationLink.statement statementLink)
    (StatementCandidateObservationLink.candidatePNFRef statementLink)
    (StatementCandidateObservationLink.parseReviewRef statementLink)
    (StatementCandidateObservationLink.semanticAdmissionReceiptRef statementLink)
    (StatementCandidateObservationLink.observationRef statementLink)
    (ObservationEventLink.eventRef eventLink)
    claims
    downstream
    true refl
    false refl
    false refl
    false refl

record ReverseTraceReceipt (trace : SemanticTracePath) : Set where
  constructor reverse-trace-receipt
  field
    eventCoordinate : String
    observationCoordinate : String
    statementCoordinate : String
    spanCoordinate : String
    revisionCoordinate : String
    eventMatches : eventCoordinate ≡ SemanticTracePath.eventRef trace
    observationMatches : observationCoordinate ≡ SemanticTracePath.observationRef trace
    statementMatches :
      statementCoordinate
      ≡ PersistentStatementIdentity.statementRef (SemanticTracePath.statement trace)
    spanMatches :
      spanCoordinate
      ≡ PersistentStatementIdentity.exactSpanRef (SemanticTracePath.statement trace)
    revisionMatches :
      revisionCoordinate
      ≡ PersistentStatementIdentity.sourceRevisionRef (SemanticTracePath.statement trace)

open ReverseTraceReceipt public

canonicalReverseTrace :
  (trace : SemanticTracePath) →
  ReverseTraceReceipt trace
canonicalReverseTrace trace =
  reverse-trace-receipt
    (SemanticTracePath.eventRef trace)
    (SemanticTracePath.observationRef trace)
    (PersistentStatementIdentity.statementRef (SemanticTracePath.statement trace))
    (PersistentStatementIdentity.exactSpanRef (SemanticTracePath.statement trace))
    (PersistentStatementIdentity.sourceRevisionRef (SemanticTracePath.statement trace))
    refl refl refl refl refl

record ForwardTraceReceipt (trace : SemanticTracePath) : Set where
  constructor forward-trace-receipt
  field
    revisionCoordinate : String
    spanCoordinate : String
    statementCoordinate : String
    observationCoordinate : String
    eventCoordinate : String
    revisionMatches :
      revisionCoordinate
      ≡ PersistentStatementIdentity.sourceRevisionRef (SemanticTracePath.statement trace)
    spanMatches :
      spanCoordinate
      ≡ PersistentStatementIdentity.exactSpanRef (SemanticTracePath.statement trace)
    statementMatches :
      statementCoordinate
      ≡ PersistentStatementIdentity.statementRef (SemanticTracePath.statement trace)
    observationMatches : observationCoordinate ≡ SemanticTracePath.observationRef trace
    eventMatches : eventCoordinate ≡ SemanticTracePath.eventRef trace

open ForwardTraceReceipt public

canonicalForwardTrace :
  (trace : SemanticTracePath) →
  ForwardTraceReceipt trace
canonicalForwardTrace trace =
  forward-trace-receipt
    (PersistentStatementIdentity.sourceRevisionRef (SemanticTracePath.statement trace))
    (PersistentStatementIdentity.exactSpanRef (SemanticTracePath.statement trace))
    (PersistentStatementIdentity.statementRef (SemanticTracePath.statement trace))
    (SemanticTracePath.observationRef trace)
    (SemanticTracePath.eventRef trace)
    refl refl refl refl refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TracePathCreatesEvidencePayment : Set where
data TracePathCreatesSemanticAdmission : Set where
data TracePathCreatesApplicability : Set where
data TracePathCreatesClaimTruth : Set where
data EventDisplayMetadataMayReplaceReverseIndex : Set where

tracePathDoesNotCreateEvidencePayment :
  TracePathCreatesEvidencePayment → ⊥
tracePathDoesNotCreateEvidencePayment ()

tracePathDoesNotCreateSemanticAdmission :
  TracePathCreatesSemanticAdmission → ⊥
tracePathDoesNotCreateSemanticAdmission ()

tracePathDoesNotCreateApplicability :
  TracePathCreatesApplicability → ⊥
tracePathDoesNotCreateApplicability ()

tracePathDoesNotCreateClaimTruth :
  TracePathCreatesClaimTruth → ⊥
tracePathDoesNotCreateClaimTruth ()

displayMetadataCannotReplaceReverseIndex :
  EventDisplayMetadataMayReplaceReverseIndex → ⊥
displayMetadataCannotReplaceReverseIndex ()

record M12PersistentTraceBoundary : Set where
  constructor m12-persistent-trace-boundary
  field
    statementIdentitySeparateFromParserRun : Bool
    sourceToEventForwardTraversal : Bool
    eventToSourceReverseTraversal : Bool
    reverseIndexExplicit : Bool
    traceCreatesSemanticAuthority : Bool
    traceCreatesClaimTruth : Bool

canonicalM12PersistentTraceBoundary : M12PersistentTraceBoundary
canonicalM12PersistentTraceBoundary =
  m12-persistent-trace-boundary
    true true true true false false
