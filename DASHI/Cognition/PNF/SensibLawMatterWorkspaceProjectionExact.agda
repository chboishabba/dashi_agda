module DASHI.Cognition.PNF.SensibLawMatterWorkspaceProjectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMatterContextProjectionExact as Context
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Chronology
import DASHI.Cognition.PNF.SensibLawCandidateEventDiscoveryExact as Discovery
import DASHI.Cognition.PNF.SensibLawOperationalSemanticBoundaryExact as Operational
import DASHI.Cognition.PNF.SensibLawReviewWorkstationExact as Review
import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace

------------------------------------------------------------------------
-- S30.B generic Matter projection.
--
-- The Matter workspace composes already-owned semantic/read models.  It is
-- not another persistence store and does not create a universal timeline.
------------------------------------------------------------------------

record KnowledgeTimelineCoordinate : Set where
  constructor knowledge-timeline-coordinate
  field
    semanticRef : String
    sourceRevisionRef : String
    knowledgeTimeRef : String
    knowledgeMembership : Context.KnowledgeCutMembership
    sourceRoleRef : String
    messageTimeEqualsEventTime : Bool
    messageTimeEqualsEventTimeIsFalse :
      messageTimeEqualsEventTime ≡ false

open KnowledgeTimelineCoordinate public

record GenericMatterWorkspace : Set where
  constructor generic-matter-workspace
  field
    matterRef : String
    context : Context.MatterContext

    sourceTraceRefs : List String
    eventTimelineRefs : List String
    knowledgeTimeline : List KnowledgeTimelineCoordinate
    operationalTimelineRefs : List String
    propositionRefs : List String
    claimRefs : List String
    suggestedJoinRefs : List String
    reviewItemRefs : List String
    legalProofRefs : List String
    researchRefs : List String
    workProductRefs : List String
    handoffRefs : List String

    oneCanonicalWorld : Bool
    oneCanonicalWorldIsTrue : oneCanonicalWorld ≡ true

    projectionOnly : Bool
    projectionOnlyIsTrue : projectionOnly ≡ true

    contextFiltersAllViews : Bool
    contextFiltersAllViewsIsTrue : contextFiltersAllViews ≡ true

    eventKnowledgeOperationalTimesDistinct : Bool
    eventKnowledgeOperationalTimesDistinctIsTrue :
      eventKnowledgeOperationalTimesDistinct ≡ true

    createsUniversalTimeline : Bool
    createsUniversalTimelineIsFalse : createsUniversalTimeline ≡ false

    mutatesCanonicalWorld : Bool
    mutatesCanonicalWorldIsFalse : mutatesCanonicalWorld ≡ false

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open GenericMatterWorkspace public

canonicalGenericMatterWorkspace : GenericMatterWorkspace
canonicalGenericMatterWorkspace =
  generic-matter-workspace
    "matter:example"
    Context.canonicalMatterContext
    []
    []
    []
    []
    []
    []
    []
    []
    []
    []
    []
    []
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Five-question product contract.
------------------------------------------------------------------------

record MatterFiveQuestionBoundary : Set where
  constructor matter-five-question-boundary
  field
    whatHappened : Bool
    whatWasSaid : Bool
    whatWasKnownWhen : Bool
    whatWasDoneWithKnowledge : Bool
    whatMayBeUsedOrDisclosed : Bool

    oneQuestionMayReplaceAnother : Bool
    oneQuestionMayReplaceAnotherIsFalse :
      oneQuestionMayReplaceAnother ≡ false

canonicalMatterFiveQuestionBoundary : MatterFiveQuestionBoundary
canonicalMatterFiveQuestionBoundary =
  matter-five-question-boundary
    true
    true
    true
    true
    true
    false refl

------------------------------------------------------------------------
-- Existing subsystem welds are projection references only.
------------------------------------------------------------------------

record MatterSubsystemBoundary : Set where
  constructor matter-subsystem-boundary
  field
    semanticTraceReused : Bool
    chronologyReused : Bool
    automaticJoinProposalReused : Bool
    operationalTimelineReused : Bool
    reviewQueueReused : Bool

    duplicatesM12TraceStore : Bool
    duplicatesChronologyStore : Bool
    duplicatesReviewStore : Bool

canonicalMatterSubsystemBoundary : MatterSubsystemBoundary
canonicalMatterSubsystemBoundary =
  matter-subsystem-boundary
    true true true true true
    false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MatterWorkspaceIsNewWorld : Set where
data MatterWorkspaceCreatesUniversalTimeline : Set where
data EventTimeEqualsKnowledgeTime : Set where
data KnowledgeTimeEqualsOperationalTime : Set where
data OperationalTimeEqualsEventTime : Set where
data MatterProjectionCreatesSemanticAuthority : Set where
data HiddenCoordinateIsFalse : Set where
data HiddenCoordinateIsAbsentFromWorld : Set where
data OperationalUnresolvedBecomesReviewPending : Set where
data OperationalUnresolvedBecomesSemanticUnresolved : Set where
data OperationalUnresolvedBecomesUserPriority : Set where
data SuggestedJoinIsCanonicalEvent : Set where
data ReviewAcceptedMeansClaimTrue : Set where

matterWorkspaceIsNotNewWorld : MatterWorkspaceIsNewWorld → ⊥
matterWorkspaceIsNotNewWorld ()

matterWorkspaceDoesNotCreateUniversalTimeline :
  MatterWorkspaceCreatesUniversalTimeline → ⊥
matterWorkspaceDoesNotCreateUniversalTimeline ()

eventTimeDoesNotEqualKnowledgeTime :
  EventTimeEqualsKnowledgeTime → ⊥
eventTimeDoesNotEqualKnowledgeTime ()

knowledgeTimeDoesNotEqualOperationalTime :
  KnowledgeTimeEqualsOperationalTime → ⊥
knowledgeTimeDoesNotEqualOperationalTime ()

operationalTimeDoesNotEqualEventTime :
  OperationalTimeEqualsEventTime → ⊥
operationalTimeDoesNotEqualEventTime ()

matterProjectionDoesNotCreateSemanticAuthority :
  MatterProjectionCreatesSemanticAuthority → ⊥
matterProjectionDoesNotCreateSemanticAuthority ()

hiddenCoordinateDoesNotBecomeFalse :
  HiddenCoordinateIsFalse → ⊥
hiddenCoordinateDoesNotBecomeFalse ()

hiddenCoordinateDoesNotLeaveWorld :
  HiddenCoordinateIsAbsentFromWorld → ⊥
hiddenCoordinateDoesNotLeaveWorld ()

operationalUnresolvedDoesNotBecomeReviewPending :
  OperationalUnresolvedBecomesReviewPending → ⊥
operationalUnresolvedDoesNotBecomeReviewPending ()

operationalUnresolvedDoesNotBecomeSemanticUnresolved :
  OperationalUnresolvedBecomesSemanticUnresolved → ⊥
operationalUnresolvedDoesNotBecomeSemanticUnresolved ()

operationalUnresolvedDoesNotBecomeUserPriority :
  OperationalUnresolvedBecomesUserPriority → ⊥
operationalUnresolvedDoesNotBecomeUserPriority ()

suggestedJoinDoesNotBecomeCanonicalEvent :
  SuggestedJoinIsCanonicalEvent → ⊥
suggestedJoinDoesNotBecomeCanonicalEvent ()

reviewAcceptedDoesNotMeanClaimTrue :
  ReviewAcceptedMeansClaimTrue → ⊥
reviewAcceptedDoesNotMeanClaimTrue ()
