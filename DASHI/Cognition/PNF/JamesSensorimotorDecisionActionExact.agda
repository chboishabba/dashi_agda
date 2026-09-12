module DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.NeuralDecisionProducerBridgeExact as Neural
import DASHI.Cognition.PNF.DecisionStateBundleExact as Bundle
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- Source-bound formalisation of:
--
-- Thomas W. James,
-- "Sensorimotor Mechanisms of Decisions and Actions",
-- Journal of Cognitive Neuroscience 38(6), 1089-1100 (2026),
-- DOI 10.1162/JOCN.a.2484.
--
-- Earlier manifestation retained separately:
-- DOI 10.20944/preprints202507.0979.v1.
--
-- Citation identifies the proposal being formalised. It imports neither
-- proof nor authority, and this owner does not promote the paper into a
-- theorem about metaphysical free will or determinism.
------------------------------------------------------------------------

publishedDOI : String
publishedDOI = "10.1162/JOCN.a.2484"

preprintDOI : String
preprintDOI = "10.20944/preprints202507.0979.v1"

publishedSource : Source.AttributedSource
publishedSource = Source.mkDOISource
  "Thomas W. James"
  "Sensorimotor Mechanisms of Decisions and Actions"
  "Journal of Cognitive Neuroscience 38(6), 1089-1100"
  "2026"
  publishedDOI
  "https://doi.org/10.1162/JOCN.a.2484"
  Source.academicArticleSource
  "source-paying published perspective for the sensorimotor/active-sensing formalisation; citation does not import proof or authority"
  Source.publicAttribution

preprintSource : Source.AttributedSource
preprintSource = Source.mkDOISource
  "Thomas W. James"
  "Sensorimotor Mechanisms of Decisions and Actions"
  "Preprints.org"
  "2025"
  preprintDOI
  "https://doi.org/10.20944/preprints202507.0979.v1"
  Source.academicArticleSource
  "earlier manifestation retained for chronology and wording comparison; not conflated with the published paper"
  Source.publicAttribution

publishedCitationImportsNoProof :
  Source.citationImportsProof publishedSource ≡ false
publishedCitationImportsNoProof = Source.citationImportsProofIsFalse publishedSource

publishedCitationCreatesNoAuthority :
  Source.citationCreatesAuthority publishedSource ≡ false
publishedCitationCreatesNoAuthority = Source.citationCreatesAuthorityIsFalse publishedSource

------------------------------------------------------------------------
-- Finite recurrent carrier. The model is deliberately small: it witnesses the
-- causal geometry James asks experiments to preserve, not a complete theory of
-- biological decision making.
------------------------------------------------------------------------

data EnvironmentState : Set where
  neutralEnvironment : EnvironmentState
  supportChangedEnvironment : EnvironmentState
  counterChangedEnvironment : EnvironmentState

data BodyState : Set where
  neutralBody : BodyState
  supportActuatedBody : BodyState
  counterActuatedBody : BodyState

data SensoryState : Set where
  neutralSensation : SensoryState
  supportFeedback : SensoryState
  counterFeedback : SensoryState

data SensorimotorState : Set where
  supportSensorimotor : SensorimotorState
  counterSensorimotor : SensorimotorState

record SensorimotorEpisode : Set where
  constructor sensorimotorEpisode
  field
    environment : EnvironmentState
    body : BodyState
    sensory : SensoryState
    mechanism : SensorimotorState
    action : Decision.ExecutedAction
    learning : Memory.MemoryFibre

open SensorimotorEpisode public

nextEnvironment : Decision.ExecutedAction → EnvironmentState → EnvironmentState
nextEnvironment Decision.noAction env = env
nextEnvironment Decision.supportAction _ = supportChangedEnvironment
nextEnvironment Decision.counterAction _ = counterChangedEnvironment

nextBody : Decision.ExecutedAction → BodyState → BodyState
nextBody Decision.noAction bodyState = bodyState
nextBody Decision.supportAction _ = supportActuatedBody
nextBody Decision.counterAction _ = counterActuatedBody

sense : EnvironmentState → BodyState → SensoryState
sense neutralEnvironment neutralBody = neutralSensation
sense supportChangedEnvironment _ = supportFeedback
sense counterChangedEnvironment _ = counterFeedback
sense neutralEnvironment supportActuatedBody = supportFeedback
sense neutralEnvironment counterActuatedBody = counterFeedback

activeSensingStep : SensorimotorEpisode → SensorimotorEpisode
activeSensingStep episode =
  let env′ = nextEnvironment (action episode) (environment episode)
      body′ = nextBody (action episode) (body episode)
  in sensorimotorEpisode
       env′
       body′
       (sense env′ body′)
       (mechanism episode)
       (action episode)
       (learning episode)

supportActionChangesNextSensation : (memory : Memory.MemoryFibre) →
  sensory
    (activeSensingStep
      (sensorimotorEpisode neutralEnvironment neutralBody neutralSensation
        supportSensorimotor Decision.supportAction memory))
  ≡ supportFeedback
supportActionChangesNextSensation memory = refl

counterActionChangesNextSensation : (memory : Memory.MemoryFibre) →
  sensory
    (activeSensingStep
      (sensorimotorEpisode neutralEnvironment neutralBody neutralSensation
        counterSensorimotor Decision.counterAction memory))
  ≡ counterFeedback
counterActionChangesNextSensation memory = refl

sameInitialSensationDifferentActionsDifferentNextSensation :
  (memory : Memory.MemoryFibre) →
  sensory
    (activeSensingStep
      (sensorimotorEpisode neutralEnvironment neutralBody neutralSensation
        supportSensorimotor Decision.supportAction memory))
  ≡ sensory
    (activeSensingStep
      (sensorimotorEpisode neutralEnvironment neutralBody neutralSensation
        counterSensorimotor Decision.counterAction memory)) → ⊥
sameInitialSensationDifferentActionsDifferentNextSensation memory ()

------------------------------------------------------------------------
-- Learning-through-active-sensing reuses MemoryFibre rather than introducing
-- another memory ontology. `reinforce` is a finite DASHI witness of an
-- experience-dependent update; it is not attributed to James as a unique
-- biological learning law.
------------------------------------------------------------------------

learningThroughActiveSensing : Memory.MemoryFibre → Memory.MemoryFibre
learningThroughActiveSensing = Memory.reinforce

activeSensingLearningPreservesRememberedEvent :
  (memory : Memory.MemoryFibre) →
  Memory.rememberedEvent (learningThroughActiveSensing memory)
  ≡ Memory.rememberedEvent memory
activeSensingLearningPreservesRememberedEvent memory = refl

activeSensingLearningIncrementsActionWeight :
  (memory : Memory.MemoryFibre) →
  Memory.actionWeight (learningThroughActiveSensing memory)
  ≡ suc (Memory.actionWeight memory)
activeSensingLearningIncrementsActionWeight memory = refl

------------------------------------------------------------------------
-- Same observed action can arise from distinct task-achieving sensorimotor
-- states. Therefore the action projection does not recover mechanism state.
------------------------------------------------------------------------

observedActionProjection : SensorimotorEpisode → Decision.ExecutedAction
observedActionProjection = action

sensorimotorProjection : SensorimotorEpisode → SensorimotorState
sensorimotorProjection = mechanism

supportMechanismEpisode : Memory.MemoryFibre → SensorimotorEpisode
supportMechanismEpisode memory =
  sensorimotorEpisode neutralEnvironment neutralBody neutralSensation
    supportSensorimotor Decision.noAction memory

counterMechanismEpisode : Memory.MemoryFibre → SensorimotorEpisode
counterMechanismEpisode memory =
  sensorimotorEpisode neutralEnvironment neutralBody neutralSensation
    counterSensorimotor Decision.noAction memory

sameObservedActionDifferentSensorimotorState :
  (memory : Memory.MemoryFibre) →
  observedActionProjection (supportMechanismEpisode memory)
  ≡ observedActionProjection (counterMechanismEpisode memory)
sameObservedActionDifferentSensorimotorState memory = refl

sensorimotorStatesStillDiffer :
  (memory : Memory.MemoryFibre) →
  sensorimotorProjection (supportMechanismEpisode memory)
  ≡ sensorimotorProjection (counterMechanismEpisode memory) → ⊥
sensorimotorStatesStillDiffer memory ()

sensorimotorActionNonFactorabilityWitness :
  (memory : Memory.MemoryFibre) →
  NF.NonFactorabilityWitness observedActionProjection sensorimotorProjection
sensorimotorActionNonFactorabilityWitness memory =
  NF.nonFactorabilityWitness
    (supportMechanismEpisode memory)
    (counterMechanismEpisode memory)
    (sameObservedActionDifferentSensorimotorState memory)
    (sensorimotorStatesStillDiffer memory)

observedActionDoesNotRecoverSensorimotorState :
  (memory : Memory.MemoryFibre) →
  NF.FactorsThrough observedActionProjection sensorimotorProjection → ⊥
observedActionDoesNotRecoverSensorimotorState memory =
  NF.witnessRulesOutEveryFlatFactorisation
    (sensorimotorActionNonFactorabilityWitness memory)

------------------------------------------------------------------------
-- Phenomenon/mechanism WrongType boundary. The empty permissions are explicit
-- no-promotion surfaces: no function in this owner can silently identify the
-- phenomenological label with its physical producer/update.
------------------------------------------------------------------------

data DecisionPhenomenon : Set where
  reportedDecision : DecisionPhenomenon

data DecisionMechanism : Set where
  taskAchievingSensorimotorMechanism : DecisionMechanism

data MemoryDescription : Set where
  reportedMemory : MemoryDescription

data LearningUpdate : Set where
  physicalLearningUpdate : LearningUpdate

data DecisionPhenomenonMechanismCollapsePermission : Set where

data MemoryDescriptionLearningUpdateCollapsePermission : Set where

decisionPhenomenonIsNotMechanism :
  DecisionPhenomenonMechanismCollapsePermission → ⊥
decisionPhenomenonIsNotMechanism ()

memoryDescriptionIsNotLearningUpdate :
  MemoryDescriptionLearningUpdateCollapsePermission → ⊥
memoryDescriptionIsNotLearningUpdate ()

record JamesWrongTypeBoundary : Set where
  constructor jamesWrongTypeBoundary
  field
    decisionPhenomenonEqualsMechanism : Bool
    decisionPhenomenonEqualsExecutedAction : Bool
    memoryDescriptionEqualsLearningUpdate : Bool
    attentionLabelEqualsAttentionMechanism : Bool
    oneCircuitDefinesDecision : Bool
    reportedDecisionActionCorrelationProvesCausalArrow : Bool
    paperProvesDeterminism : Bool
    paperProvesLibertarianFreeWill : Bool

open JamesWrongTypeBoundary public

canonicalJamesWrongTypeBoundary : JamesWrongTypeBoundary
canonicalJamesWrongTypeBoundary =
  jamesWrongTypeBoundary false false false false false false false false

jamesDoesNotProveDeterminism :
  paperProvesDeterminism canonicalJamesWrongTypeBoundary ≡ false
jamesDoesNotProveDeterminism = refl

jamesDoesNotProveLibertarianFreeWill :
  paperProvesLibertarianFreeWill canonicalJamesWrongTypeBoundary ≡ false
jamesDoesNotProveLibertarianFreeWill = refl

------------------------------------------------------------------------
-- Explicit reuse receipts: the James specialization composes with the repo's
-- existing decision bundle and neural-producer boundaries rather than
-- replacing them.
------------------------------------------------------------------------

existingActionProjectionIsLossy :
  (memory : Memory.MemoryFibre) →
  NF.FactorsThrough Bundle.observedAction Bundle.commitmentState → ⊥
existingActionProjectionIsLossy = Bundle.actionCannotRecoverCommitmentFromBundle

existingNeuralProducerDoesNotDefineOneDecisionCircuit :
  Neural.NeuralDecisionProducerBoundary.oneCircuitDefinesDecision
    Neural.canonicalNeuralDecisionProducerBoundary
  ≡ false
existingNeuralProducerDoesNotDefineOneDecisionCircuit = refl

------------------------------------------------------------------------
-- Optional cybernetic specialization: a controlled variable and reference
-- signal can specialize the recurrent carrier without being made universal.
------------------------------------------------------------------------

data ControlSignal : Set where
  lowSignal : ControlSignal
  highSignal : ControlSignal

record SensorimotorControlSpecialization : Set where
  constructor sensorimotorControlSpecialization
  field
    referenceSignal : ControlSignal
    controlledVariable : ControlSignal
    errorSignal : ControlSignal
    universalDefinitionClaimed : Bool

canonicalControlSpecialization : SensorimotorControlSpecialization
canonicalControlSpecialization =
  sensorimotorControlSpecialization highSignal lowSignal highSignal false
