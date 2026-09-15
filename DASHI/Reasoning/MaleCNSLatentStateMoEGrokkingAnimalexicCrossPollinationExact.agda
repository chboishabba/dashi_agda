module DASHI.Reasoning.MaleCNSLatentStateMoEGrokkingAnimalexicCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact as Routing
import DASHI.Biology.SpectralGrokkingLatticeExact as Spectral
import DASHI.Biology.AnimalexicLexicIntegrationExact as Lexic
import DASHI.Biology.AnimalexicDrosophilaEmbodiedBridge as FlyLexic
import DASHI.Biology.ConsciousAccessCoalition as Access

------------------------------------------------------------------------
-- MALECNS LATENT-STATE / MoE / GROKKING / ANIMALEXIC CROSS-POLLINATION
--
-- This owner composes existing theorem surfaces. It does not identify a
-- predictive latent with a biological mechanism, an E8-like chart with the
-- ontology of a fly brain, a behavioural motif with semantic meaning, or an
-- access-consciousness candidate with phenomenal consciousness.
------------------------------------------------------------------------

data RoutingState : Set where
  diffuseRouting : RoutingState
  compactRouting : RoutingState

data LatentState : Set where
  unresolvedLatent : LatentState
  stableLatent : LatentState

data GeometryState : Set where
  unconstrainedGeometry : GeometryState
  lowRankGeometry : GeometryState
  sparseGeometry : GeometryState
  latticeGeometry : GeometryState
  e8CandidateGeometry : GeometryState

data SemanticHypothesis : Set where
  defensiveArousalHypothesis : SemanticHypothesis
  negativeValenceHypothesis : SemanticHypothesis
  threatExpectationHypothesis : SemanticHypothesis
  fearLikeHypothesis : SemanticHypothesis
  positiveValenceHypothesis : SemanticHypothesis
  motivationalDriveHypothesis : SemanticHypothesis
  preferenceHypothesis : SemanticHypothesis
  phenomenalFearHypothesis : SemanticHypothesis
  subjectiveJoyHypothesis : SemanticHypothesis

------------------------------------------------------------------------
-- Routing and representation-change donors.
------------------------------------------------------------------------

routingAdequacyDoesNotPromoteMechanism :
  Routing.heldOutAdequacyImpliesPhysicalMechanism
    Routing.canonicalFibreRoutingCrossPollinationBoundary ≡ false
routingAdequacyDoesNotPromoteMechanism = refl

moeRemainsAnalogyNotLiteralBrainArchitecture :
  Routing.mixtureOfExpertsIsLiteralBrainArchitecture
    Routing.canonicalFibreRoutingCrossPollinationBoundary ≡ false
moeRemainsAnalogyNotLiteralBrainArchitecture = refl

learningMayChangeConsumerCarryingFibres :
  Routing.learningMayChangeWhichFibresCarryTheConsumer
    Routing.canonicalFibreRoutingCrossPollinationBoundary ≡ true
learningMayChangeConsumerCarryingFibres = refl

grokkingCleanupRetainsDeclaredSymmetryModes :
  Spectral.symmetryAdaptedComponentCount Spectral.cleanupPhase ≡ 3
grokkingCleanupRetainsDeclaredSymmetryModes =
  Routing.cleanupRetainsSymmetryModes

------------------------------------------------------------------------
-- LILA/E8 is a candidate latent atlas only.
------------------------------------------------------------------------

e8GeometryDoesNotPromoteBiologicalOntology :
  Routing.lilaE8ExplainsFlyStructureFunctionResult
    Routing.canonicalFibreRoutingCrossPollinationBoundary ≡ false
e8GeometryDoesNotPromoteBiologicalOntology = refl

record GeometryCandidateBoundary : Set where
  constructor geometry-candidate-boundary
  field
    unconstrainedLatentComesFirst : Bool
    lowRankIsCandidateCompression : Bool
    sparseRoutingIsCandidateCompression : Bool
    latticeIsCandidateAtlas : Bool
    e8IsCandidateAtlas : Bool
    candidateAtlasEqualsPhysicalMechanism : Bool
    candidateAtlasEqualsPhysicalMechanismIsFalse :
      candidateAtlasEqualsPhysicalMechanism ≡ false

canonicalGeometryCandidateBoundary : GeometryCandidateBoundary
canonicalGeometryCandidateBoundary =
  geometry-candidate-boundary true true true true true false refl

------------------------------------------------------------------------
-- Animalexic semantic discipline.
------------------------------------------------------------------------

behaviouralMotifDoesNotPromoteSemanticMeaning :
  Lexic.behaviouralSyllableDoesNotSupplyMeaning
    Lexic.canonicalAnimalLexicIntegrationBoundary ≡ true
behaviouralMotifDoesNotPromoteSemanticMeaning = refl

semanticEquivalenceRemainsExperimentRelative :
  Lexic.semanticEquivalenceIsExperimentLanguageRelative
    Lexic.canonicalAnimalLexicIntegrationBoundary ≡ true
semanticEquivalenceRemainsExperimentRelative = refl

semanticDebtRemainsConsumerIndexed :
  Lexic.semanticDebtIsConsumerIndexed
    Lexic.canonicalAnimalLexicIntegrationBoundary ≡ true
semanticDebtRemainsConsumerIndexed = refl

flyNeuralStateDoesNotEqualBehaviourMotif : FlyLexic.DrosophilaAnimalexicBoundary
flyNeuralStateDoesNotEqualBehaviourMotif =
  FlyLexic.noNeuralStateEqualsBehaviourMotif

flyFunctionalCorrelationDoesNotEqualCommunicativeAct :
  FlyLexic.DrosophilaAnimalexicBoundary
flyFunctionalCorrelationDoesNotEqualCommunicativeAct =
  FlyLexic.noFunctionalCorrelationEqualsCommunicativeAct

------------------------------------------------------------------------
-- Interactive semantic refinement: identical current observations do not
-- establish semantic equivalence if an admissible interaction separates the
-- hidden states.
------------------------------------------------------------------------

record InteractiveSemanticRefinement
    (State Interaction Observation Meaning : Set) : Set₁ where
  constructor interactiveSemanticRefinement
  field
    observe : State → Observation
    step : Interaction → State → State
    meaning : State → Meaning
    left : State
    right : State
    sameCurrentObservation : observe left ≡ observe right
    separatingInteraction : Interaction
    postInteractionSeparates :
      observe (step separatingInteraction left)
      ≡ observe (step separatingInteraction right) → ⊥

open InteractiveSemanticRefinement public

interactiveSemanticRefinementRetainsCollision :
  ∀ {State Interaction Observation Meaning}
    (witness : InteractiveSemanticRefinement State Interaction Observation Meaning) →
  observe witness (left witness) ≡ observe witness (right witness)
interactiveSemanticRefinementRetainsCollision = sameCurrentObservation

------------------------------------------------------------------------
-- Joint consumer family. Separate success on isolated consumers is not
-- automatically promoted into a joint-family theorem.
------------------------------------------------------------------------

record JointConsumerAdequacy
    (State Consumer : Set) : Set₁ where
  constructor jointConsumerAdequacy
  field
    adequateFor : Consumer → State → Set
    familyReceipt : String

open JointConsumerAdequacy public

data SeparateConsumerAdequacyImpliesJointAdequacy : Set where

consumerFamilyAdequacyIsJoint :
  SeparateConsumerAdequacyImpliesJointAdequacy → ⊥
consumerFamilyAdequacyIsJoint ()

------------------------------------------------------------------------
-- Three distinct compression axes.
------------------------------------------------------------------------

data CompressionKind : Set where
  routingCompression : CompressionKind
  geometricCompression : CompressionKind
  semanticCompression : CompressionKind

routingNotGeometric : routingCompression ≡ geometricCompression → ⊥
routingNotGeometric ()

geometricNotSemantic : geometricCompression ≡ semanticCompression → ⊥
geometricNotSemantic ()

routingNotSemantic : routingCompression ≡ semanticCompression → ⊥
routingNotSemantic ()

compressionKindsRemainDistinct :
  (routingCompression ≡ geometricCompression → ⊥)
  × (geometricCompression ≡ semanticCompression → ⊥)
  × (routingCompression ≡ semanticCompression → ⊥)
compressionKindsRemainDistinct =
  routingNotGeometric , geometricNotSemantic , routingNotSemantic

------------------------------------------------------------------------
-- Conscious-access/sentience firewall.
------------------------------------------------------------------------

phenomenalIdentityRemainsUnpaid :
  Access.phenomenalIdentityPromoted Access.canonicalConsciousAccessCoalition
  ≡ false
phenomenalIdentityRemainsUnpaid =
  Access.canonicalCoalitionPhenomenalIdentityNotPromoted

------------------------------------------------------------------------
-- Programme boundary.
------------------------------------------------------------------------

record LatentStateProgrammeBoundary : Set where
  constructor latent-state-programme-boundary
  field
    routingCoalitionSurfaceReused : Bool
    grokkingRepresentationChangeSurfaceReused : Bool
    e8CandidateGeometrySurfaceReused : Bool
    animalexicSemanticRefinementSurfaceReused : Bool
    consumerFamilyIsQueryIndexed : Bool
    routingCompressionDistinctFromGeometryCompression : Bool
    geometryCompressionDistinctFromSemanticCompression : Bool
    latentPredictionImpliesBiologicalMechanism : Bool
    latentPredictionImpliesBiologicalMechanismIsFalse :
      latentPredictionImpliesBiologicalMechanism ≡ false
    e8FitImpliesFlyBrainIsE8 : Bool
    e8FitImpliesFlyBrainIsE8IsFalse :
      e8FitImpliesFlyBrainIsE8 ≡ false
    behaviouralPredictionImpliesSubjectiveExperience : Bool
    behaviouralPredictionImpliesSubjectiveExperienceIsFalse :
      behaviouralPredictionImpliesSubjectiveExperience ≡ false
    empiricalAffectLabelPaid : Bool
    empiricalAffectLabelPaidIsFalse : empiricalAffectLabelPaid ≡ false
    independentTrialReplicationPaid : Bool
    independentTrialReplicationPaidIsFalse : independentTrialReplicationPaid ≡ false
    crossAnimalReplicationPaid : Bool
    crossAnimalReplicationPaidIsFalse : crossAnimalReplicationPaid ≡ false
    interpretation : String

open LatentStateProgrammeBoundary public

canonicalLatentStateProgrammeBoundary : LatentStateProgrammeBoundary
canonicalLatentStateProgrammeBoundary =
  latent-state-programme-boundary
    true
    true
    true
    true
    true
    true
    true
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Formal integration only: routing coalitions, grokking-style representation change, candidate latent geometry, Animalexic semantic refinement, and joint consumer obligations are composed without promoting predictive adequacy to biological mechanism or subjective phenomenology."

------------------------------------------------------------------------
-- Cross-repo attribution coordinate: runtime Animalexic remains its own repo.
-- This is metadata/provenance, not empirical payment.
------------------------------------------------------------------------

record AnimalexicRuntimeSource : Set where
  constructor animalexic-runtime-source
  field
    repository : String
    commit : String
    architecturePath : String
    governanceReading : String

canonicalAnimalexicRuntimeSource : AnimalexicRuntimeSource
canonicalAnimalexicRuntimeSource =
  animalexic-runtime-source
    "github.com/chboishabba/animalexic"
    "8f0ee8bb07c4788601306de67a0f97edc0e9a0dd"
    "architecture.md"
    "Candidate generation is separated from governed promotion/canonical state mutation; runtime metadata does not promote fly affect semantics."
