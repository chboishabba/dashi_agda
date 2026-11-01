module DASHI.Core.ResidualActionSalienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismModelDiscriminationExact as Model
import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- CONSUMER- / CONTEXT-RELATIVE RESIDUAL SALIENCE
--
-- Residual magnitude or class does not determine importance in isolation.
-- Salience depends on the live hypothesis set, dependency carrier, consumer and
-- action authority.  The same residual may therefore justify different next
-- actions for different consumers without any contradiction in the evidence.
------------------------------------------------------------------------

data SalienceClass : Set where
  dormantSalience : SalienceClass
  relevantSalience : SalienceClass
  discriminatingForConsumer : SalienceClass
  actionCriticalSalience : SalienceClass


record SalienceContext : Set where
  constructor salienceContext
  field
    consumerReference : String
    liveHypothesisReference : String
    dependencyReference : String
    authorityReference : String

open SalienceContext public

record ResidualSalienceReceipt : Set where
  constructor residualSalienceReceipt
  field
    residual : Model.ModelResidual
    context : SalienceContext
    salience : SalienceClass
    salienceBasis : String
    provenanceReference : String

open ResidualSalienceReceipt public

record SalienceConditionedAction : Set where
  constructor salienceConditionedAction
  field
    salienceReceipt : ResidualSalienceReceipt
    selectedKind : Action.ResidualActionKind
    actionBasis : String
    admissionReference : String

open SalienceConditionedAction public

------------------------------------------------------------------------
-- Exact finite fixture showing consumer-relative action without changing the
-- evidence carrier.  The fixture is deliberately independent of one concrete
-- ModelResidual value: it establishes the action/context non-collapse that the
-- general record exposes for real residuals.
------------------------------------------------------------------------

data FixtureConsumer : Set where
  mechanismConsumer : FixtureConsumer
  operationalConsumer : FixtureConsumer


data FixtureAction : Set where
  measureForMechanism : FixtureAction
  holdForOperation : FixtureAction


fixtureAction : FixtureConsumer → FixtureAction
fixtureAction mechanismConsumer = measureForMechanism
fixtureAction operationalConsumer = holdForOperation

sameEvidenceReference : FixtureConsumer → String
sameEvidenceReference _ = "same retained evidence and residual carrier"

measureIsNotHold : measureForMechanism ≡ holdForOperation → ⊥
measureIsNotHold ()

consumerChangeCanChangeAction :
  fixtureAction mechanismConsumer ≡ fixtureAction operationalConsumer → ⊥
consumerChangeCanChangeAction ()

------------------------------------------------------------------------
-- Dormancy is not permanent irrelevance.  This seam reuses the existing
-- reopenable-hypothesis forest so dependency/evidence changes may reactivate a
-- formerly dormant hypothesis and thereby alter residual salience.
------------------------------------------------------------------------

record ReopenedSalienceReceipt : Set₁ where
  constructor reopenedSalienceReceipt
  field
    hypothesis : Model.ModelHypothesis
    semantics : Forest.HypothesisSemantics Model.ModelHypothesis
    reason : Forest.DormancyReason
    reopeningEvidence : Forest.ReopeningEvidence semantics reason hypothesis
    transition :
      Forest.HypothesisTransition semantics hypothesis
        (Forest.reopenable reason) Forest.active
    salienceAfterReopen : SalienceClass
    salienceReference : String

open ReopenedSalienceReceipt public

record ResidualActionSalienceBoundary : Set where
  constructor residualActionSalienceBoundary
  field
    residualClassAloneDeterminesSalience : Bool
    residualClassAloneDeterminesSalienceIsFalse :
      residualClassAloneDeterminesSalience ≡ false

    sameResidualRequiresSameActionAcrossConsumers : Bool
    sameResidualRequiresSameActionAcrossConsumersIsFalse :
      sameResidualRequiresSameActionAcrossConsumers ≡ false

    consumerChangeMayAlterActionWithoutEvidenceChange : Bool
    consumerChangeMayAlterActionWithoutEvidenceChangeIsTrue :
      consumerChangeMayAlterActionWithoutEvidenceChange ≡ true

    highSalienceCreatesActionAuthority : Bool
    highSalienceCreatesActionAuthorityIsFalse :
      highSalienceCreatesActionAuthority ≡ false

    dormantHypothesisIsPermanentlyIrrelevant : Bool
    dormantHypothesisIsPermanentlyIrrelevantIsFalse :
      dormantHypothesisIsPermanentlyIrrelevant ≡ false

canonicalResidualActionSalienceBoundary : ResidualActionSalienceBoundary
canonicalResidualActionSalienceBoundary =
  residualActionSalienceBoundary false refl false refl true refl false refl false refl

existingResidualActionBoundary : Action.ResidualActionBoundary
existingResidualActionBoundary = Action.canonicalResidualActionBoundary

existingHypothesisBoundary : Forest.ReopenableHypothesisBoundary
existingHypothesisBoundary = Forest.canonicalReopenableHypothesisBoundary
