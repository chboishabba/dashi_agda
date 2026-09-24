module DASHI.Cognition.PNF.SensibLawOperationalSemanticBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S28.SB operational-state / semantic-world boundary.
--
-- Operational events record what the operator/system was doing. Semantic
-- events record what allegedly/observably happened in the matter/world.
-- They may be linked by reviewed reference without being collapsed.
------------------------------------------------------------------------

data OperationalEventKind : Set where
  session toolActivity researchActivity reviewAction gitCommit pullRequest :
    OperationalEventKind
  taskTransition interruption browserActivity editorActivity :
    OperationalEventKind
  communicationActivity other : OperationalEventKind

record OperationalEvent : Set where
  constructor operational-event
  field
    operationalEventRef : String
    producerEventRef : String
    producerRef : String
    stateDate : String
    startTimeRef : String
    endTimeRef : String
    primaryAppRef : String
    label : String
    provenanceRefs : List String
    kind : OperationalEventKind
    producerObserved : Bool
    producerObservedIsTrue : producerObserved ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    paysEvidence : Bool
    paysEvidenceIsFalse : paysEvidence ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open OperationalEvent public

data OperationalTargetKind : Set where
  matter source statement parserReceipt observation semanticEvent proposition :
    OperationalTargetKind
  claim authority reviewItem artifact researchResidual : OperationalTargetKind

data OperationalSemanticRelationKind : Set where
  opened observed edited parsed reviewed researched followedAuthority :
    OperationalSemanticRelationKind
  acceptedReview rejectedReview qualifiedReview requestedEvidence :
    OperationalSemanticRelationKind
  producedArtifact committedChange affected : OperationalSemanticRelationKind

record OperationalSemanticLink : Set where
  constructor operational-semantic-link
  field
    linkRef : String
    operationalEventRef : String
    targetRef : String
    targetKind : OperationalTargetKind
    relationKind : OperationalSemanticRelationKind
    relationshipReceiptRef : String
    reviewedLink : Bool
    reviewedLinkIsTrue : reviewedLink ≡ true
    createsSemanticIdentity : Bool
    createsSemanticIdentityIsFalse : createsSemanticIdentity ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    paysEvidence : Bool
    paysEvidenceIsFalse : paysEvidence ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open OperationalSemanticLink public

------------------------------------------------------------------------
-- StatiBaker producer boundary.
------------------------------------------------------------------------

record StatiBakerActivityEventBoundary : Set where
  constructor statibaker-activity-event-boundary
  field
    producerAlgorithmRef : String
    producerEventRef : String
    startTimeRef : String
    endTimeRef : String
    snapshotRefs : List String
    primaryAppRef : String
    producerTitle : String
    inputHashRef : String
    policyReceiptRef : String
    downstreamMayResegmentTime : Bool
    downstreamMayReplaceProducerEvent : Bool
    activityCreatesSemanticTruth : Bool

canonicalStatiBakerActivityEventBoundary : StatiBakerActivityEventBoundary
canonicalStatiBakerActivityEventBoundary =
  statibaker-activity-event-boundary
    "sb.sessionize.v0"
    "producer-event-ref"
    "producer-start"
    "producer-end"
    []
    "producer-app"
    "producer-title"
    "producer-input-hash"
    "producer-policy-receipt"
    false false false

------------------------------------------------------------------------
-- Golden distinctions.
------------------------------------------------------------------------

record OperationalSemanticGoldenBoundary : Set where
  constructor operational-semantic-golden-boundary
  field
    operationalStateDistinctFromSemanticWorld : Bool
    operationalEventDistinctFromWorldEvent : Bool
    taskCompletionCreatesPropositionTruth : Bool
    sessionContinuityCreatesSemanticIdentity : Bool
    toolUseCreatesEndorsement : Bool
    openedSourcePaysEvidence : Bool
    reviewActivityCreatesAdmissionWithoutReceipt : Bool
    agentOutputCreatesWorldFact : Bool

canonicalOperationalSemanticGoldenBoundary :
  OperationalSemanticGoldenBoundary
canonicalOperationalSemanticGoldenBoundary =
  operational-semantic-golden-boundary
    true true false false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OperationalEventIsWorldEvent : Set where
data TaskCompletionCreatesTruth : Set where
data SessionContinuityCreatesIdentity : Set where
data ToolUseCreatesEndorsement : Set where
data OpenedSourcePaysEvidence : Set where
data ReviewActivityCreatesAdmission : Set where
data AgentOutputCreatesWorldFact : Set where
data StatiBakerEventMayBeResegmentedDownstream : Set where
data OperationalLinkCreatesSemanticIdentity : Set where

operationalEventIsNotWorldEvent : OperationalEventIsWorldEvent → ⊥
operationalEventIsNotWorldEvent ()

taskCompletionDoesNotCreateTruth : TaskCompletionCreatesTruth → ⊥
taskCompletionDoesNotCreateTruth ()

sessionContinuityDoesNotCreateIdentity :
  SessionContinuityCreatesIdentity → ⊥
sessionContinuityDoesNotCreateIdentity ()

toolUseDoesNotCreateEndorsement : ToolUseCreatesEndorsement → ⊥
toolUseDoesNotCreateEndorsement ()

openedSourceDoesNotPayEvidence : OpenedSourcePaysEvidence → ⊥
openedSourceDoesNotPayEvidence ()

reviewActivityNeedsSeparateAdmissionReceipt :
  ReviewActivityCreatesAdmission → ⊥
reviewActivityNeedsSeparateAdmissionReceipt ()

agentOutputDoesNotCreateWorldFact : AgentOutputCreatesWorldFact → ⊥
agentOutputDoesNotCreateWorldFact ()

statibakerTimeMayNotBeResegmentedDownstream :
  StatiBakerEventMayBeResegmentedDownstream → ⊥
statibakerTimeMayNotBeResegmentedDownstream ()

operationalLinkDoesNotCreateSemanticIdentity :
  OperationalLinkCreatesSemanticIdentity → ⊥
operationalLinkDoesNotCreateSemanticIdentity ()
