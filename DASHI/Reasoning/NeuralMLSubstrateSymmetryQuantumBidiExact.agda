module DASHI.Reasoning.NeuralMLSubstrateSymmetryQuantumBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi
import DASHI.Biology.NeuralFixedTransverseObserverBridgeExact as NeuralObserver
import DASHI.Reasoning.NeuralSpectralRelationCrossPollinationExact as NeuralSpectral
import DASHI.Reasoning.DASHIgGrokkingEmpiricalBridgeExact as Grokking
import DASHI.Programmes.QuantumCHSHDiscriminatorExact as Quantum
import DASHI.Governance.ConsciousnessPhysicalDiscriminatorSynthesisExact as Consciousness

------------------------------------------------------------------------
-- NEURAL / ML / SUBSTRATE / SYMMETRY / QUANTUM BIDI
--
-- Neural networks are permitted to reuse coarse neuroscientific ideas as
-- productive forward abstractions without identifying those abstractions with
-- biological mechanism.  The recurring collision is:
--
--   same task behaviour / same coarse computation
--     != same learned representation
--     != same realised causal topology
--     != same physical substrate
--     != same phenomenal instantiation.
--
-- Grokking and symmetry structure therefore become candidate discriminators of
-- learned representation, while quantum experiments are a distinct physical
-- discriminator lane.  None is promoted into the others by analogy alone.
------------------------------------------------------------------------

data AbstractionLayer : Set where
  behaviouralSurface
  statisticalFunction
  learnedRepresentation
  realisedCausalTopology
  physicalSubstrate
  phenomenalInstantiation
  : AbstractionLayer

record NeuralMLBidiReceipt : Set where
  constructor neural-ml-bidi-receipt
  field
    behaviouralConsumerReference : String
    coarseNeuroscienceObserverReference : String
    trainingDataReference : String
    architectureReference : String
    learnedRepresentationReference : String
    symmetryOrSpectralReference : String
    realisedTopologyReference : String
    physicalSubstrateReference : String
    discriminatorReference : String
    observationProvenanceReference : String
    nuisanceReference : String
    backwardConsumerReference : String
    nextExperimentReference : String

------------------------------------------------------------------------
-- Canonical imported boundaries.
------------------------------------------------------------------------

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

neuralObserverBoundary : NeuralObserver.NeuralObserverBridgeBoundary
neuralObserverBoundary = NeuralObserver.canonicalNeuralObserverBridgeBoundary

neuralSpectralBoundary : NeuralSpectral.NeuralSpectralRelationBoundary
neuralSpectralBoundary = NeuralSpectral.canonicalNeuralSpectralRelationBoundary

grokkingBoundary : Grokking.DASHIgGrokkingEmpiricalBoundary
grokkingBoundary = Grokking.canonicalDASHIgGrokkingEmpiricalBoundary

quantumBoundary : Quantum.QuantumCHSHBoundary
quantumBoundary = Quantum.canonicalQuantumCHSHBoundary

consciousnessBoundary : Consciousness.ConsciousnessPhysicalDiscriminatorBoundary
consciousnessBoundary = Consciousness.canonicalConsciousnessPhysicalDiscriminatorBoundary

------------------------------------------------------------------------
-- Exact inherited non-collapses.
------------------------------------------------------------------------

fmriLikeCollisionDoesNotRecoverRelationalMode :
  NeuralObserver.sameCoarseReadoutImpliesSameRelationalMode neuralObserverBoundary ≡ false
fmriLikeCollisionDoesNotRecoverRelationalMode = refl

coarseNeuralMeasurementDoesNotRecoverRelationalVariation :
  NeuralSpectral.coarseMeasurementDeterminesRelationalVariation neuralSpectralBoundary ≡ false
coarseNeuralMeasurementDoesNotRecoverRelationalVariation = refl

grokkingSuccessDoesNotIdentifyLearningMechanism :
  Grokking.perfectFinalAccuracyIdentifiesLearningMechanism grokkingBoundary ≡ false
grokkingSuccessDoesNotIdentifyLearningMechanism = refl

spectralCompressionIsNotAutomaticallyFutureSafe :
  NeuralSpectral.spectralCompressionAutomaticallyFutureSafe neuralSpectralBoundary ≡ false
spectralCompressionIsNotAutomaticallyFutureSafe = refl

chshCalibrationDoesNotClosePhysicalTheoryPromotion :
  Quantum.chshCalibrationDischargesPhysicalPromotionGate quantumBoundary ≡ false
chshCalibrationDoesNotClosePhysicalTheoryPromotion = refl

physicalDiscriminatorDoesNotAutomaticallyProveConsciousness :
  Consciousness.discriminatorResultAutomaticallyProvesConsciousness consciousnessBoundary ≡ false
physicalDiscriminatorDoesNotAutomaticallyProveConsciousness = refl

------------------------------------------------------------------------
-- Cross-domain boundary.
------------------------------------------------------------------------

record NeuralMLSubstrateSymmetryQuantumBoundary : Set where
  constructor neural-ml-substrate-symmetry-quantum-boundary
  field
    neuralNetworkIsLiteralCoarseGrainedBrain : Bool
    neuralNetworkIsLiteralCoarseGrainedBrainIsFalse :
      neuralNetworkIsLiteralCoarseGrainedBrain ≡ false
    sameBehaviourAndComputationIdentifiesRepresentation : Bool
    sameBehaviourAndComputationIdentifiesRepresentationIsFalse :
      sameBehaviourAndComputationIdentifiesRepresentation ≡ false
    sameLearnedRepresentationIdentifiesPhysicalSubstrate : Bool
    sameLearnedRepresentationIdentifiesPhysicalSubstrateIsFalse :
      sameLearnedRepresentationIdentifiesPhysicalSubstrate ≡ false
    symmetryAdaptedLearningProvesBiologicalMechanism : Bool
    symmetryAdaptedLearningProvesBiologicalMechanismIsFalse :
      symmetryAdaptedLearningProvesBiologicalMechanism ≡ false
    classicalAndQuantumImplementationsWithSameTaskSurfaceArePhysicallyIdentical : Bool
    classicalAndQuantumImplementationsWithSameTaskSurfaceArePhysicallyIdenticalIsFalse :
      classicalAndQuantumImplementationsWithSameTaskSurfaceArePhysicallyIdentical ≡ false
    coarseNeuroscienceCanStillSupplyUsefulForwardInductiveBias : Bool
    coarseNeuroscienceCanStillSupplyUsefulForwardInductiveBiasIsTrue :
      coarseNeuroscienceCanStillSupplyUsefulForwardInductiveBias ≡ true
    grokkingAndSymmetryCanSupplyRepresentationDiscriminators : Bool
    grokkingAndSymmetryCanSupplyRepresentationDiscriminatorsIsTrue :
      grokkingAndSymmetryCanSupplyRepresentationDiscriminators ≡ true
    physicalSubstrateQuestionsRequireIndependentPhysicalDiscriminators : Bool
    physicalSubstrateQuestionsRequireIndependentPhysicalDiscriminatorsIsTrue :
      physicalSubstrateQuestionsRequireIndependentPhysicalDiscriminators ≡ true
    reading : String

canonicalNeuralMLSubstrateSymmetryQuantumBoundary :
  NeuralMLSubstrateSymmetryQuantumBoundary
canonicalNeuralMLSubstrateSymmetryQuantumBoundary =
  neural-ml-substrate-symmetry-quantum-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    "Neural networks may productively borrow coarse neural/connectomic observer structure as forward inductive bias, but behavioural equality, statistical function, learned representation, realised causal topology, physical substrate and phenomenology remain separately typed. Grokking/symmetry can discriminate representations; quantum/physical questions require their own experimental lane; backward BIDI admission prevents analogy from becoming mechanism or ontology."
