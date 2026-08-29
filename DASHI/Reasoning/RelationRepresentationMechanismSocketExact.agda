module DASHI.Reasoning.RelationRepresentationMechanismSocketExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RELATION-REPRESENTATION MECHANISM SOCKET
--
-- Cross-pollinated from the Stage-7 / LES DomainMechanismSocket pattern in
-- draft #637.  Purpose: freeze the weakest application-facing surface that a
-- real embedding/activation experiment must supply before local sensitivity,
-- discrepancy, intervention or mechanism claims can be interpreted.
--
-- This is not a second Stage-7 inference calculus.  It is an upstream producer
-- socket intended to feed the generic #636 owners once they are merged.
------------------------------------------------------------------------

record RelationMechanismSocket : Set₁ where
  constructor relationMechanismSocket
  field
    State : Set
    Context : Set
    Representation : Set
    Experiment : Set
    Observation : Set
    Residual : Set

    encode : Context → State → Representation
    applyRepresentationExperiment : Experiment → Representation → Representation
    observe : Representation → Observation
    experimentObserve : Context → Experiment → State → Observation
    discrepancyCarrier : Context → Experiment → State → Residual

    experimentObservationCommutes :
      (context : Context) →
      (experiment : Experiment) →
      (state : State) →
      experimentObserve context experiment state
      ≡ observe
          (applyRepresentationExperiment experiment (encode context state))

open RelationMechanismSocket public

------------------------------------------------------------------------
-- A candidate mathematical family becomes a mechanism claim only with an
-- independently supplied realization/causal interpretation receipt.
------------------------------------------------------------------------

record MechanismInterpretationReceipt (socket : RelationMechanismSocket) : Set₁ where
  constructor mechanismInterpretationReceipt
  field
    interventionSemantics : Set
    statePerturbationSemantics : Set
    representationExperimentMatchesIntervention : Set
    discrepancyHasDeclaredMeaning : Set
    sourceAndProducerProvenanceReceipt : Set

open MechanismInterpretationReceipt public

record RelationMechanismBoundary : Set where
  constructor relationMechanismBoundary
  field
    fittedTranslationIsMechanismByDefault : Bool
    fittedTranslationIsMechanismByDefaultIsFalse :
      fittedTranslationIsMechanismByDefault ≡ false

    fittedRotationIsMechanismByDefault : Bool
    fittedRotationIsMechanismByDefaultIsFalse :
      fittedRotationIsMechanismByDefault ≡ false

    fittedManifoldIsMechanismByDefault : Bool
    fittedManifoldIsMechanismByDefaultIsFalse :
      fittedManifoldIsMechanismByDefault ≡ false

    finiteDifferenceIsCausalJacobianByDefault : Bool
    finiteDifferenceIsCausalJacobianByDefaultIsFalse :
      finiteDifferenceIsCausalJacobianByDefault ≡ false

    explicitDiscrepancyCarrierRequiredForStage7 : Bool
    explicitDiscrepancyCarrierRequiredForStage7IsTrue :
      explicitDiscrepancyCarrierRequiredForStage7 ≡ true

    actualExperimentObservationMustCommute : Bool
    actualExperimentObservationMustCommuteIsTrue :
      actualExperimentObservationMustCommute ≡ true

canonicalRelationMechanismBoundary : RelationMechanismBoundary
canonicalRelationMechanismBoundary =
  relationMechanismBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl

------------------------------------------------------------------------
-- Empty admission state for the motivating Instagram experiment.
-- No real activation carrier / intervention map is presently supplied.
------------------------------------------------------------------------

record CurrentMechanismAvailability : Set where
  constructor currentMechanismAvailability
  field
    realActivationStateCarrierSupplied : Bool
    realContextCarrierSupplied : Bool
    realInterventionExperimentSupplied : Bool
    realDiscrepancyCarrierSupplied : Bool
    causalMechanismReceiptSupplied : Bool
    reading : String

currentInstagramMechanismAvailability : CurrentMechanismAvailability
currentInstagramMechanismAvailability =
  currentMechanismAvailability
    false false false false false
    "The branch is experiment-ready but does not possess the actual activation/state/context/intervention payload needed to instantiate a real mechanism socket for eigenslur or flourishing."
