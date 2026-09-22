module DASHI.Interop.SharedUserWorldConsumerRuntimeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Interop.SharedUserWorldConsumerRuntimeExact as Shared

journalObservation : Shared.SharedWorldCoordinate
journalObservation =
  Shared.shared-world-coordinate
    "world:journal:event-1"
    Shared.observationCoordinate
    Shared.journalSource
    "source:journal:day-1"
    "revision:journal:day-1:v1"
    "prov:journal:event-1"
    Shared.explicitlyReviewed
    "context:private-day-1"
    "scope:user-plus-lawyer-selected-slice"
    false refl
    false refl

privateHypothesis : Shared.SharedWorldCoordinate
privateHypothesis =
  Shared.shared-world-coordinate
    "world:journal:hypothesis-1"
    Shared.hypothesisCoordinate
    Shared.journalSource
    "source:journal:day-1"
    "revision:journal:day-1:v1"
    "prov:journal:hypothesis-1"
    Shared.observerOnly
    "context:private-day-1"
    "scope:user-only"
    false refl
    false refl

missionObservation : Shared.SharedWorldCoordinate
missionObservation =
  Shared.shared-world-coordinate
    "world:mission:actual-1"
    Shared.missionCoordinate
    Shared.observerCaptureSource
    "source:openrecall:capture-1"
    "revision:capture:1"
    "prov:capture:1"
    Shared.observerOnly
    "context:work-session-1"
    "scope:user-mission"
    false refl
    false refl

lawyerSlice : Shared.ConsumerDependencySlice
lawyerSlice =
  Shared.consumer-dependency-slice
    "consumer:lawyer:matter-1"
    Shared.lawyerMatterConsumer
    ("world:journal:event-1" ∷ [])
    "scope:user-plus-lawyer-selected-slice"
    "query:what-supports-allegation-1"
    "slice:lawyer:matter-1"

journalSlice : Shared.ConsumerDependencySlice
journalSlice =
  Shared.consumer-dependency-slice
    "consumer:journal:reconstruction"
    Shared.personalJournalConsumer
    ("world:journal:event-1" ∷ "world:journal:hypothesis-1" ∷ [])
    "scope:user-only"
    "query:what-happened-around-period-1"
    "slice:journal:reconstruction"

missionSlice : Shared.ConsumerDependencySlice
missionSlice =
  Shared.consumer-dependency-slice
    "consumer:mission:actual-vs-should"
    Shared.missionActualVsShouldConsumer
    ("world:mission:actual-1" ∷ [])
    "scope:user-mission"
    "query:actual-vs-should"
    "slice:mission"

reviewedSelectedJournalEventReusesForLawyer :
  Shared.decideSharedWorldReuse true true true
  ≡ Shared.reuseAlreadyPaid
reviewedSelectedJournalEventReusesForLawyer = refl

privateUnreviewedHypothesisDoesNotLeakToLawyer :
  Shared.decideSharedWorldReuse true false false
  ≡ Shared.scopeBlocked
privateUnreviewedHypothesisDoesNotLeakToLawyer = refl

observerMissionCaptureStillNeedsReviewForStrongerUse :
  Shared.decideSharedWorldReuse true true false
  ≡ Shared.researchMissing
observerMissionCaptureStillNeedsReviewForStrongerUse = refl

unrelatedCoordinateDoesNotBecomeJoinByAdjacency :
  Shared.decideSharedWorldReuse false true true
  ≡ Shared.researchMissing
unrelatedCoordinateDoesNotBecomeJoinByAdjacency = refl

sharedDelta : Shared.ReviewedWorldDelta
sharedDelta =
  Shared.reviewed-world-delta
    "delta:shared-world:1"
    ("world:journal:event-1" ∷ [])
    []
    []
    "review:journal:event-1"
    "prov:delta:shared-world:1"
    false refl
    false refl

affectedConsumers : Shared.AffectedConsumerRecomputation
affectedConsumers =
  Shared.affected-consumer-recomputation
    sharedDelta
    (journalSlice ∷ lawyerSlice ∷ [])
    "recompute:journal-plus-lawyer"
    true refl
    false refl
    false refl

revisionMaintenance : Shared.RevisionMaintenanceDelta
revisionMaintenance =
  Shared.revision-maintenance-delta
    "world:journal:event-1"
    "revision:journal:day-1:v1"
    "revision:journal:day-1:v2"
    ("world:journal:event-1" ∷ [])
    ("review:journal:event-1" ∷ [])
    "maintenance:journal-event-1"
