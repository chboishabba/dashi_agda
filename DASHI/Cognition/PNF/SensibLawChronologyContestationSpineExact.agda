module DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace

------------------------------------------------------------------------
-- S28 chronology + human contestation.
--
-- These are semantic carriers over the existing M12 source/statement/
-- observation/event spine.  Time uncertainty is represented explicitly;
-- competing accounts remain distinct leaves under a proposition root; and
-- contestation is a typed relation rather than a scalar flag.
------------------------------------------------------------------------

data TemporalForm : Set where
  exactInstant : String → TemporalForm
  exactDate : String → TemporalForm
  interval : String → String → TemporalForm
  approximate : String → TemporalForm
  relativeBefore : String → TemporalForm
  relativeAfter : String → TemporalForm
  contemporaneous : String → TemporalForm
  undated : TemporalForm
  unknown : TemporalForm

record TemporalAssertion : Set where
  constructor temporal-assertion
  field
    temporalRef : String
    form : TemporalForm
    statementRefs : List String
    observationRefs : List String
    reviewRef : String
    sourceTraceRelationshipRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open TemporalAssertion public

data ClaimLeafKind : Set where
  affirmation denial qualification alternativeAccount : ClaimLeafKind

data ClaimReviewState : Set where
  unreviewed accepted rejected abstained qualified superseded : ClaimReviewState

record PropositionRoot : Set where
  constructor proposition-root
  field
    propositionRef : String
    label : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open PropositionRoot public

record ClaimLeaf (root : PropositionRoot) : Set where
  constructor claim-leaf
  field
    claimRef : String
    kind : ClaimLeafKind
    speakerRef : String
    statementRefs : List String
    observationRefs : List String
    temporalRefs : List String
    scopeRefs : List String
    reviewState : ClaimReviewState
    reviewRef : String
    sourceTraceRelationshipRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ClaimLeaf public

data ContestationRelationKind : Set where
  supports qualifies denies contradicts adjacent supersedes :
    ContestationRelationKind
  sameIncidentDifferentAccount unresolvedRelation :
    ContestationRelationKind

record ContestationRelation
    {rootA rootB : PropositionRoot}
    (left : ClaimLeaf rootA)
    (right : ClaimLeaf rootB) : Set where
  constructor contestation-relation
  field
    relationRef : String
    kind : ContestationRelationKind
    statementRefs : List String
    observationRefs : List String
    reviewRef : String
    sourceTraceRelationshipRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ContestationRelation public

------------------------------------------------------------------------
-- Chronology projection keeps uncertainty typed.
------------------------------------------------------------------------

data ChronologyPlacement : Set where
  exactPlacement approximatePlacement relativeOnlyPlacement :
    ChronologyPlacement
  undatedPlacement unknownPlacement : ChronologyPlacement

placement : TemporalForm → ChronologyPlacement
placement (exactInstant _) = exactPlacement
placement (exactDate _) = exactPlacement
placement (interval _ _) = exactPlacement
placement (approximate _) = approximatePlacement
placement (relativeBefore _) = relativeOnlyPlacement
placement (relativeAfter _) = relativeOnlyPlacement
placement (contemporaneous _) = relativeOnlyPlacement
placement undated = undatedPlacement
placement unknown = unknownPlacement

record ChronologyEntry : Set where
  constructor chronology-entry
  field
    eventRef : String
    temporal : TemporalAssertion
    statementRefs : List String
    observationRefs : List String
    propositionRefs : List String
    claimRefs : List String
    contestationRelationRefs : List String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ChronologyEntry public

chronologyPlacement :
  (entry : ChronologyEntry) →
  ChronologyPlacement
chronologyPlacement entry = placement (TemporalAssertion.form (ChronologyEntry.temporal entry))

------------------------------------------------------------------------
-- M12 trace weld: chronology drill-down reuses the existing source trace.
------------------------------------------------------------------------

record ChronologySourceTrace (entry : ChronologyEntry) : Set where
  constructor chronology-source-trace
  field
    trace : Trace.SemanticTracePath
    eventMatches :
      Trace.SemanticTracePath.eventRef trace ≡ ChronologyEntry.eventRef entry
    relationshipRef : String

open ChronologySourceTrace public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data UnknownDateMeansMissingEvent : Set where
data RelativeOrderCreatesExactTimestamp : Set where
data SharedPropositionRootMergesClaimLeaves : Set where
data ContestationIsScalarBoolean : Set where
data ReviewStateCreatesClaimTruth : Set where
data ChronologyProjectionCreatesAuthority : Set where
data TimelineDisplayMayReplaceSourceTrace : Set where

unknownDateDoesNotEraseEvent : UnknownDateMeansMissingEvent → ⊥
unknownDateDoesNotEraseEvent ()

relativeOrderDoesNotCreateExactTimestamp :
  RelativeOrderCreatesExactTimestamp → ⊥
relativeOrderDoesNotCreateExactTimestamp ()

sharedRootDoesNotMergeClaimLeaves :
  SharedPropositionRootMergesClaimLeaves → ⊥
sharedRootDoesNotMergeClaimLeaves ()

contestationIsNotScalarBoolean : ContestationIsScalarBoolean → ⊥
contestationIsNotScalarBoolean ()

reviewStateDoesNotCreateClaimTruth : ReviewStateCreatesClaimTruth → ⊥
reviewStateDoesNotCreateClaimTruth ()

chronologyProjectionDoesNotCreateAuthority :
  ChronologyProjectionCreatesAuthority → ⊥
chronologyProjectionDoesNotCreateAuthority ()

timelineDisplayCannotReplaceSourceTrace :
  TimelineDisplayMayReplaceSourceTrace → ⊥
timelineDisplayCannotReplaceSourceTrace ()

record S28ChronologyContestationBoundary : Set where
  constructor s28-chronology-contestation-boundary
  field
    exactApproxRelativeUndatedUnknownDistinct : Bool
    propositionRootSeparateFromClaimLeaf : Bool
    contestationRelationTyped : Bool
    sourceTraceReused : Bool
    timelineCreatesSemanticAuthority : Bool
    reviewCreatesClaimTruth : Bool

canonicalS28ChronologyContestationBoundary :
  S28ChronologyContestationBoundary
canonicalS28ChronologyContestationBoundary =
  s28-chronology-contestation-boundary
    true true true true false false
