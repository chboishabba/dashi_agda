module DASHI.Reasoning.FibreRoutingInterventionExperimentGrokkingObservableExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Action
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Reasoning.FibreRoutingSufficiencyCausalInterventionSnowballExact as Causal
import DASHI.Reasoning.FibreRoutingMDLAlgorithmicGeneralizationGrokkingSnowballExact as Algorithmic
import DASHI.Reasoning.FibreRoutingCompressionLadderExact as Ladder

------------------------------------------------------------------------
-- OPERATIONAL FRONTIER
--
-- 1. observationally equivalent candidate representations expose an
--    intervention-identification obstruction;
-- 2. the existing ActionabilityCostedExperimentChoice machinery selects the
--    cheapest declared discriminator that actually resolves that obstruction;
-- 3. C_t(Q) is represented as an executable minimum adequate-carrier cost over
--    a finite time-indexed fixture.
--
-- This is an experiment/search adapter, not a claim that the illustrative
-- finite fixture is an empirical grokking law.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Finite causal discrimination specimen.
------------------------------------------------------------------------

data CandidateWorld : Set where
  observationalTwinA observationalTwinB : CandidateWorld

data InterventionControl : Set where
  perturbRelevantCoordinate : InterventionControl

data ExperimentalValue : Set where
  low high : ExperimentalValue

data ExperimentalDimension : Set where
  observationalDimension interventionResponseDimension : ExperimentalDimension

data CausalCoordinate : Set where
  observationalPredictionCoordinate interventionResponseCoordinate : CausalCoordinate

coordinateRole : CausalCoordinate → Experiment.CoordinateRole
coordinateRole observationalPredictionCoordinate = Experiment.measuredObservable
coordinateRole interventionResponseCoordinate = Experiment.derivedDiscriminator

coordinateDimension : CausalCoordinate → ExperimentalDimension
coordinateDimension observationalPredictionCoordinate = observationalDimension
coordinateDimension interventionResponseCoordinate = interventionResponseDimension

coordinateRead : CausalCoordinate → CandidateWorld → ExperimentalValue
coordinateRead observationalPredictionCoordinate observationalTwinA = low
coordinateRead observationalPredictionCoordinate observationalTwinB = low
coordinateRead interventionResponseCoordinate observationalTwinA = low
coordinateRead interventionResponseCoordinate observationalTwinB = high

applyIntervention : InterventionControl → CandidateWorld → CandidateWorld
applyIntervention perturbRelevantCoordinate world = world

causalExperimentDesign :
  Experiment.ExperimentalCoordinateDesign
    CandidateWorld InterventionControl ExperimentalValue ExperimentalDimension
causalExperimentDesign = Experiment.experimentalCoordinateDesign
  CausalCoordinate
  coordinateRole
  coordinateDimension
  coordinateRead
  applyIntervention
  coordinateReference
  dimensionReference
  derivationReference
  controlReference
  where
  coordinateReference : CausalCoordinate → String
  coordinateReference observationalPredictionCoordinate =
    "observational prediction shared by candidate representations"
  coordinateReference interventionResponseCoordinate =
    "derived intervention-response discriminator"

  dimensionReference : CausalCoordinate → String
  dimensionReference observationalPredictionCoordinate = "prediction surface"
  dimensionReference interventionResponseCoordinate = "intervention response"

  derivationReference : CausalCoordinate → String
  derivationReference observationalPredictionCoordinate =
    "direct declared observational read"
  derivationReference interventionResponseCoordinate =
    "candidate-specific response under the declared intervention semantics"

  controlReference : InterventionControl → String
  controlReference perturbRelevantCoordinate =
    "declared perturbation used only to separate observationally equivalent candidates"

observationalProjection : CandidateWorld → ExperimentalValue
observationalProjection = coordinateRead observationalPredictionCoordinate

interventionCoordinateSeparatesObservationalTwins :
  Experiment.CoordinateSeparatesCollision causalExperimentDesign observationalProjection
interventionCoordinateSeparatesObservationalTwins =
  Experiment.coordinateSeparatesCollision
    interventionResponseCoordinate
    observationalTwinA
    observationalTwinB
    refl
    (λ ())

------------------------------------------------------------------------
-- Cheapest declared experiment that resolves the causal ambiguity.
------------------------------------------------------------------------

observeAgain : Action.InformationMove
observeAgain = Action.informationMove
  Action.takeMeasurement 1
  "repeat the existing observational prediction measurement"
  "same observation language"
  "declared but known not to discriminate the causal collision"

perturbAndRead : Action.InformationMove
perturbAndRead = Action.informationMove
  Action.perturbAndMeasure 2
  "perturb the relevant coordinate and read the intervention response"
  "one controlled perturbation plus response measurement"
  "declared discriminator; authority/safety remains independently required"

fullMechanismStudy : Action.InformationMove
fullMechanismStudy = Action.informationMove
  Action.increaseFidelity 3
  "escalate to a richer mechanistic carrier that also separates the candidates"
  "higher-cost representation/measurement study"
  "declared resolving fallback; not selected when the cheaper perturbation suffices"

data InterventionObstruction : Set where
  observationalEquivalence : InterventionObstruction

data ResolvesIntervention : Action.InformationMove → InterventionObstruction → Set where
  perturbationResolves : ResolvesIntervention perturbAndRead observationalEquivalence
  fullStudyResolves : ResolvesIntervention fullMechanismStudy observationalEquivalence

causalActionabilityProblem : Action.ActionabilityProblem
causalActionabilityProblem = Action.actionabilityProblem
  InterventionObstruction
  observationalEquivalence
  ResolvesIntervention
  "two candidate representations make the same observational prediction but differ under the declared intervention"
  "intervention-predictive adequacy consumer"
  "experiment selection does not create intervention authority"

data DeclaredMove : Action.InformationMove → Set where
  observeDeclared : DeclaredMove observeAgain
  perturbDeclared : DeclaredMove perturbAndRead
  fullStudyDeclared : DeclaredMove fullMechanismStudy

selectedPerturbation : Action.ResolvingMove causalActionabilityProblem
selectedPerturbation = Action.resolvingMove perturbAndRead perturbationResolves

selectedPerturbationIsCheapest :
  Action.CheapestResolvingMove causalActionabilityProblem DeclaredMove
selectedPerturbationIsCheapest = Action.cheapestResolvingMove
  selectedPerturbation
  perturbDeclared
  minimal
  "declared comparison set = observe-again cost 1, perturb-and-read cost 2, full mechanism study cost 3; only the latter two resolve the causal collision"
  where
  minimal :
    (alternative : Action.InformationMove) →
    DeclaredMove alternative →
    ResolvesIntervention alternative observationalEquivalence →
    Action.cost perturbAndRead ≤ Action.cost alternative
  minimal .perturbAndRead perturbDeclared perturbationResolves =
    s≤s (s≤s z≤n)
  minimal .fullMechanismStudy fullStudyDeclared fullStudyResolves =
    s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Executable finite C_t(Q) specimen.
--
-- C_t(Q) = minimum declared carrier cost among carriers adequate for Q at t.
-- Here Q is a held-out relation/generalization consumer and the fixture is only
-- a regression specimen showing how a falling adequate-carrier cost is encoded.
------------------------------------------------------------------------

data TrainingCheckpoint : Set where
  earlyCheckpoint transitionCheckpoint lateCheckpoint : TrainingCheckpoint

data TraceCarrier : Set where
  fullTraceCarrier intermediateTraceCarrier compactTraceCarrier : TraceCarrier

traceCarrierCost : TraceCarrier → Nat
traceCarrierCost fullTraceCarrier = 3
traceCarrierCost intermediateTraceCarrier = 2
traceCarrierCost compactTraceCarrier = 1

data AdequateAt : TrainingCheckpoint → TraceCarrier → Set where
  earlyFullAdequate : AdequateAt earlyCheckpoint fullTraceCarrier

  transitionFullAdequate : AdequateAt transitionCheckpoint fullTraceCarrier
  transitionIntermediateAdequate : AdequateAt transitionCheckpoint intermediateTraceCarrier

  lateFullAdequate : AdequateAt lateCheckpoint fullTraceCarrier
  lateIntermediateAdequate : AdequateAt lateCheckpoint intermediateTraceCarrier
  lateCompactAdequate : AdequateAt lateCheckpoint compactTraceCarrier

record ConsumerCompressionMinimum (time : TrainingCheckpoint) : Set where
  constructor consumerCompressionMinimum
  field
    carrier : TraceCarrier
    adequate : AdequateAt time carrier
    minimal :
      (alternative : TraceCarrier) →
      AdequateAt time alternative →
      traceCarrierCost carrier ≤ traceCarrierCost alternative
open ConsumerCompressionMinimum public

earlyMinimum : ConsumerCompressionMinimum earlyCheckpoint
earlyMinimum = consumerCompressionMinimum
  fullTraceCarrier earlyFullAdequate
  (λ { .fullTraceCarrier earlyFullAdequate → s≤s (s≤s (s≤s z≤n)) })

transitionMinimum : ConsumerCompressionMinimum transitionCheckpoint
transitionMinimum = consumerCompressionMinimum
  intermediateTraceCarrier transitionIntermediateAdequate
  (λ
    { .fullTraceCarrier transitionFullAdequate → s≤s (s≤s z≤n)
    ; .intermediateTraceCarrier transitionIntermediateAdequate → s≤s (s≤s z≤n)
    })

lateMinimum : ConsumerCompressionMinimum lateCheckpoint
lateMinimum = consumerCompressionMinimum
  compactTraceCarrier lateCompactAdequate
  (λ
    { .fullTraceCarrier lateFullAdequate → s≤s z≤n
    ; .intermediateTraceCarrier lateIntermediateAdequate → s≤s z≤n
    ; .compactTraceCarrier lateCompactAdequate → s≤s z≤n
    })

consumerCompressionMinimum : TrainingCheckpoint → ConsumerCompressionMinimum
consumerCompressionMinimum earlyCheckpoint = earlyMinimum
consumerCompressionMinimum transitionCheckpoint = transitionMinimum
consumerCompressionMinimum lateCheckpoint = lateMinimum

CₜQ : TrainingCheckpoint → Nat
CₜQ time = traceCarrierCost (carrier (consumerCompressionMinimum time))

earlyCostIsThree : CₜQ earlyCheckpoint ≡ 3
earlyCostIsThree = refl

transitionCostIsTwo : CₜQ transitionCheckpoint ≡ 2
transitionCostIsTwo = refl

lateCostIsOne : CₜQ lateCheckpoint ≡ 1
lateCostIsOne = refl

lateCostPlusTwoEqualsEarlyCost :
  suc (suc (CₜQ lateCheckpoint)) ≡ CₜQ earlyCheckpoint
lateCostPlusTwoEqualsEarlyCost = refl

------------------------------------------------------------------------
-- Existing theoretical boundaries remain authoritative.
------------------------------------------------------------------------

causalBoundary : Causal.FibreSufficiencyCausalInterventionBoundary
causalBoundary = Causal.canonicalFibreSufficiencyCausalInterventionBoundary

algorithmicBoundary : Algorithmic.FibreMDLAlgorithmicGeneralizationGrokkingBoundary
algorithmicBoundary = Algorithmic.canonicalFibreMDLAlgorithmicGeneralizationGrokkingBoundary

compressionBoundary : Ladder.FibreCompressionLadderBoundary
compressionBoundary = Ladder.canonicalFibreCompressionLadderBoundary

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data CheapestExperimentMeansTrueMechanism : Set where
data FallingCtQMeansGrokking : Set where
data FallingCtQMeansKolmogorovCompression : Set where
data FallingCtQMeansCausalIdentification : Set where
data ExperimentResolutionCreatesAuthority : Set where

cheapestExperimentDoesNotIdentifyTrueMechanism :
  CheapestExperimentMeansTrueMechanism → ⊥
cheapestExperimentDoesNotIdentifyTrueMechanism ()

fallingCtQDoesNotByItselfEstablishGrokking : FallingCtQMeansGrokking → ⊥
fallingCtQDoesNotByItselfEstablishGrokking ()

fallingCtQDoesNotIdentifyKolmogorovMechanism :
  FallingCtQMeansKolmogorovCompression → ⊥
fallingCtQDoesNotIdentifyKolmogorovMechanism ()

fallingCtQDoesNotCreateCausalIdentification : FallingCtQMeansCausalIdentification → ⊥
fallingCtQDoesNotCreateCausalIdentification ()

experimentResolutionDoesNotCreateAuthority : ExperimentResolutionCreatesAuthority → ⊥
experimentResolutionDoesNotCreateAuthority ()

record InterventionExperimentGrokkingObservableBoundary : Set where
  constructor intervention-experiment-grokking-observable-boundary
  field
    cheapestDeclaredDiscriminatorIsExecutable : Bool
    observationalEquivalenceSeparatedByInterventionCoordinate : Bool
    ctqIsConsumerRelativeMinimumAdequateCarrierCost : Bool
    ctqCanFallAcrossTrainingFixture : Bool
    ctqFallDoesNotIdentifyMechanism : Bool
    experimentResolutionSeparatedFromAuthority : Bool
    existingCausalMdlCompressionBoundariesReused : Bool
open InterventionExperimentGrokkingObservableBoundary public

canonicalInterventionExperimentGrokkingObservableBoundary :
  InterventionExperimentGrokkingObservableBoundary
canonicalInterventionExperimentGrokkingObservableBoundary =
  intervention-experiment-grokking-observable-boundary
    true true true true true true true
