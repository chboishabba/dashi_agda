module DASHI.Core.OperationalOutcomeSelectiveReopeningBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.OperationalRealisationBidiCrossPollination2026Exact as Operational
import DASHI.Core.RuntimeFeedbackSelectiveReopeningExact as Reopen

------------------------------------------------------------------------
-- RECIPROCAL WELD: CONSUMER-DEFINED REALISED OUTCOME -> SELECTIVE REOPENING
--
-- A failed realised-outcome coordinate does not invalidate the whole history.
-- It identifies a changed consumer artifact, after which the existing runtime
-- dependency closure decides exactly which downstream obligations reopen.
------------------------------------------------------------------------

record FailedConsumerOutcome : Set where
  constructor failed-consumer-outcome
  field
    outcome : Operational.ConsumerDefinedOutcome
    failed : Operational.satisfied outcome ≡ false
    failureObservationReference : String
open FailedConsumerOutcome public

record OutcomeReopeningWeld : Set₂ where
  constructor outcome-reopening-weld
  field
    Artifact : Set
    Depends : Artifact → Artifact → Set
    failedOutcome : FailedConsumerOutcome
    changedArtifact : Artifact
    changedArtifactReference : String
    plan : Reopen.RuntimeReopeningPlan Depends
    planStartsAtChangedArtifact : Reopen.changed plan ≡ changedArtifact
    outcomeToArtifactReceipt : String
open OutcomeReopeningWeld public

record PartialOutcomeRetentionReceipt (weld : OutcomeReopeningWeld) : Set₁ where
  constructor partial-outcome-retention-receipt
  field
    retainedArtifact : OutcomeReopeningWeld.Artifact weld
    retained : Reopen.retain (OutcomeReopeningWeld.plan weld) retainedArtifact
    retentionReading : String
open PartialOutcomeRetentionReceipt public

record FailedOutcomeReopenReceipt (weld : OutcomeReopeningWeld) : Set₁ where
  constructor failed-outcome-reopen-receipt
  field
    reopenedArtifact : OutcomeReopeningWeld.Artifact weld
    reopened : Reopen.reopen (OutcomeReopeningWeld.plan weld) reopenedArtifact
    reopeningReading : String
open FailedOutcomeReopenReceipt public

data FailedOneOutcomeInvalidatesEverything : Set where

data ExecutionSuccessClosesConsumerOutcome : Set where

failedOneOutcomeDoesNotInvalidateEverything :
  FailedOneOutcomeInvalidatesEverything → ⊥
failedOneOutcomeDoesNotInvalidateEverything ()

executionSuccessDoesNotCloseConsumerOutcome :
  ExecutionSuccessClosesConsumerOutcome → ⊥
executionSuccessDoesNotCloseConsumerOutcome ()

record OperationalSelectiveReopeningBoundary : Set where
  constructor operational-selective-reopening-boundary
  field
    failedOutcomeMapsToChangedArtifact : Bool
    reopeningStillNeedsDependencyPath : Bool
    unaffectedCoordinatesMayBeRetained : Bool
    executionAndConsumerSuccessRemainDistinct : Bool

canonicalOperationalSelectiveReopeningBoundary :
  OperationalSelectiveReopeningBoundary
canonicalOperationalSelectiveReopeningBoundary =
  operational-selective-reopening-boundary true true true true
