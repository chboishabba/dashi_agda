module DASHI.Reasoning.Spacy369TwoDirectionArchitectureBidiExact where

open import DASHI.Core.Prelude

import DASHI.Reasoning.Spacy369ConsumerRevisionTemporalBidiExact as Temporal
import DASHI.Reasoning.Spacy369AdaptiveConsumerProbeSchedulerExact as Scheduler

------------------------------------------------------------------------
-- BIDI APPLIED TO THE TWO-DIRECTION ARCHITECTURE ITSELF.
--
-- A state has an explicit forward coordinate and an explicit backward
-- coordinate.  Forward evidence revision and backward consumer revision are
-- different transition classes.  Each class is required to freeze the other
-- coordinate unless a separate combined transition is explicitly supplied.
------------------------------------------------------------------------

record TwoDirectionState : Set₁ where
  constructor twoDirectionState
  field
    forward : Temporal.ForwardSpine
    backward : Temporal.BackwardSpine

open TwoDirectionState public

stateAt : Temporal.RevisionEpoch → TwoDirectionState
stateAt epoch =
  twoDirectionState (Temporal.forwardAt epoch) (Temporal.backwardAt epoch)

------------------------------------------------------------------------
-- Abstract forward revision: the evidence/semantic/logical channel may change,
-- but the declared backward demand is frozen by receipt.
------------------------------------------------------------------------

record ForwardRevision (before after : TwoDirectionState) : Set₁ where
  constructor forwardRevision
  field
    backwardFrozen : backward before ≡ backward after
    forwardRevisionReference : String

open ForwardRevision public

------------------------------------------------------------------------
-- Backward revision: declared consumer/information policy may change, but the
-- forward evidence/semantic/logical channel is frozen by receipt.
------------------------------------------------------------------------

record BackwardRevision (before after : TwoDirectionState) : Set₁ where
  constructor backwardRevision
  field
    forwardFrozen : forward before ≡ forward after
    backwardChanged :
      Temporal.selectedSchedule (backward before)
      ≡ Temporal.selectedSchedule (backward after) → ⊥
    backwardRevisionReference : String

open BackwardRevision public

operationalToSubjectStandingBackward :
  BackwardRevision
    (stateAt Temporal.operationalEpoch)
    (stateAt Temporal.subjectStandingEpoch)
operationalToSubjectStandingBackward =
  backwardRevision
    refl
    (λ ())
    "consumer revision: operational -> subject+standing"

subjectStandingToAllBackward :
  BackwardRevision
    (stateAt Temporal.subjectStandingEpoch)
    (stateAt Temporal.allConsumersEpoch)
subjectStandingToAllBackward =
  backwardRevision
    refl
    (λ ())
    "consumer revision: subject+standing -> all declared consumers"

------------------------------------------------------------------------
-- Transition tags make the architecture's two directions constructor-distinct.
------------------------------------------------------------------------

data DirectionTag : Set where
  forwardDirection backwardDirection : DirectionTag

forwardNotBackward : forwardDirection ≡ backwardDirection → ⊥
forwardNotBackward ()

------------------------------------------------------------------------
-- A combined change is NOT inferred from either one-sided transition.  It must
-- explicitly carry both receipts.  This prevents a consumer revision from
-- masquerading as a source correction, or a source correction from silently
-- mutating the acceptance language.
------------------------------------------------------------------------

record CombinedRevision (before after : TwoDirectionState) : Set₁ where
  constructor combinedRevision
  field
    forwardReceipt : ForwardRevision before after
    backwardReceipt : BackwardRevision before after
    combinedRevisionReference : String

open CombinedRevision public

------------------------------------------------------------------------
-- The concrete consumer-revision path is backward-only at the architecture
-- level: its forward coordinate is definitionally stable while the scheduler
-- changes from stop -> shared -> shared+closure.
------------------------------------------------------------------------

operationalForwardFrozen :
  forward (stateAt Temporal.operationalEpoch)
  ≡ forward (stateAt Temporal.subjectStandingEpoch)
operationalForwardFrozen = refl

subjectStandingForwardFrozen :
  forward (stateAt Temporal.subjectStandingEpoch)
  ≡ forward (stateAt Temporal.allConsumersEpoch)
subjectStandingForwardFrozen = refl

operationalBackwardActuallyChanges :
  Scheduler.schedule Scheduler.operationalOnly
  ≡ Scheduler.schedule Scheduler.subjectAndStanding → ⊥
operationalBackwardActuallyChanges ()

allConsumerBackwardActuallyChanges :
  Scheduler.schedule Scheduler.subjectAndStanding
  ≡ Scheduler.schedule Scheduler.subjectStandingAndClosure → ⊥
allConsumerBackwardActuallyChanges ()

------------------------------------------------------------------------
-- Architectural boundary.
------------------------------------------------------------------------

record Spacy369TwoDirectionArchitectureBidiBoundary : Set where
  constructor spacy369TwoDirectionArchitectureBidiBoundary
  field
    forwardAndBackwardTransitionsAreConstructorDistinct : Bool
    forwardAndBackwardTransitionsAreConstructorDistinctIsTrue :
      forwardAndBackwardTransitionsAreConstructorDistinct ≡ true
    backwardConsumerRevisionMayRewriteForwardEvidence : Bool
    backwardConsumerRevisionMayRewriteForwardEvidenceIsFalse :
      backwardConsumerRevisionMayRewriteForwardEvidence ≡ false
    forwardEvidenceRevisionMaySilentlyRewriteConsumerDemand : Bool
    forwardEvidenceRevisionMaySilentlyRewriteConsumerDemandIsFalse :
      forwardEvidenceRevisionMaySilentlyRewriteConsumerDemand ≡ false
    combinedRevisionMayBeInferredFromOneSidedRevision : Bool
    combinedRevisionMayBeInferredFromOneSidedRevisionIsFalse :
      combinedRevisionMayBeInferredFromOneSidedRevision ≡ false
    previousConsumerRelativeSufficiencyEqualsGlobalCompleteness : Bool
    previousConsumerRelativeSufficiencyEqualsGlobalCompletenessIsFalse :
      previousConsumerRelativeSufficiencyEqualsGlobalCompleteness ≡ false

canonicalSpacy369TwoDirectionArchitectureBidiBoundary :
  Spacy369TwoDirectionArchitectureBidiBoundary
canonicalSpacy369TwoDirectionArchitectureBidiBoundary =
  spacy369TwoDirectionArchitectureBidiBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
