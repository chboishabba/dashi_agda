module DASHI.Biology.AnimalexicDrosophilaEmbodiedBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalexicFormalSystemExact as Animal
import DASHI.Biology.AnimalexicLexicIntegrationExact as Lexic
import DASHI.Biology.AnimalexicAnimalUtteranceSurface as Utterance
import DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge as Fly
import DASHI.Biology.DrosophilaConnectomeFunctionalRegistrationBridge as Registration
import DASHI.Biology.DrosophilaStructureFunctionEffectorBenchmark as Benchmark
import DASHI.Biology.DrosophilaMotorEffectorPhysiologyBridge as Effector

------------------------------------------------------------------------
-- PURPOSE
--
-- Reuse Animalexic's governed observation/promotion architecture around the
-- Drosophila connectome-functional-effector programme.  This bridge does not
-- identify Animalexic behavioural semantics with fly neural state.  Instead it
-- imports the generic discipline:
--
--   substrate observation
--     -> candidate latent/body/event state
--     -> promoted/abstained/rejected state under receipts
--
-- while preserving Drosophila-specific structural, functional and physiology
-- producers.
------------------------------------------------------------------------

data DrosophilaAnimalexicBoundary : Set where
  noNeuralStateEqualsBehaviourMotif : DrosophilaAnimalexicBoundary
  noBehaviourMotifEqualsSemanticMeaning : DrosophilaAnimalexicBoundary
  noFunctionalCorrelationEqualsCommunicativeAct : DrosophilaAnimalexicBoundary
  noSingleModalityPromotion : DrosophilaAnimalexicBoundary
  noCandidateEqualsPromotedState : DrosophilaAnimalexicBoundary
  noCrossSpeciesSemanticTransferWithoutReceipt : DrosophilaAnimalexicBoundary
  noSharedSourceCountsAsIndependentEvidence : DrosophilaAnimalexicBoundary

------------------------------------------------------------------------
-- Animalexic-style timescale state split for fly experiments.
------------------------------------------------------------------------

record FlyAnimalexicState : Set₁ where
  field
    GeometryState : Set
    NeuralState : Set
    FunctionalObservationState : Set
    BodyState : Set
    EventState : Set
    ProvenanceState : Set

    geometry : GeometryState
    neural : NeuralState
    functionalObservation : FunctionalObservationState
    body : BodyState
    event : EventState
    provenance : ProvenanceState

open FlyAnimalexicState public

------------------------------------------------------------------------
-- Candidate/promotion surface.  Fast optical/behavioural/kernel outputs can
-- propose state but cannot mutate canonical state without a receipt.
------------------------------------------------------------------------

record FlyCandidatePromotion : Set₁ where
  field
    Observation : Set
    Candidate : Set
    PromotedState : Set
    Receipt : Set

    inferCandidate : Observation → Candidate
    materialise : Candidate → PromotedState
    admissibleReceipt : Observation → Candidate → Receipt → Set

    promoted : Candidate → Bool
    abstained : Candidate → Bool
    rejected : Candidate → Bool

    promotionRequiresReceipt :
      ∀ observation candidate receipt →
      candidate ≡ inferCandidate observation →
      promoted candidate ≡ true →
      admissibleReceipt observation candidate receipt

open FlyCandidatePromotion public

------------------------------------------------------------------------
-- Multimodal observation bundle.  Optical activity, pose/motion, contact and
-- environmental observations remain distinct evidential coordinates.
------------------------------------------------------------------------

record FlyMultimodalObservation : Set₁ where
  field
    OpticalTrace : Set
    VoltageTrace : Set
    EphysTrace : Set
    PostureTrace : Set
    MotionTrace : Set
    ContactTrace : Set
    EnvironmentTrace : Set

    optical : OpticalTrace
    voltage : VoltageTrace
    ephys : EphysTrace
    posture : PostureTrace
    motion : MotionTrace
    contact : ContactTrace
    environment : EnvironmentTrace

    opticalReceipt : Fly.ScientificSourceReceipt
    bodyObservationReceipt : Fly.ScientificSourceReceipt

open FlyMultimodalObservation public

------------------------------------------------------------------------
-- Behavioural motifs reuse Animalexic's crucial boundary: recurrence is not
-- meaning.  A fly gait/wing/turning motif is an empirical dynamical object.
------------------------------------------------------------------------

FlyBehaviourSyllable : Set → Set → Set → Set₁
FlyBehaviourSyllable = Lexic.BehaviourSyllable

flyBehaviourBoundary : Lexic.BehaviourSyllableBoundary
flyBehaviourBoundary = Lexic.canonicalBehaviourSyllableBoundary

------------------------------------------------------------------------
-- Registered connectome/function/effector chain with Animalexic governance.
------------------------------------------------------------------------

record GovernedFlyExperiment : Set₁ where
  field
    connectomeReceipt : Fly.ScientificSourceReceipt
    registrationReceipt : Fly.ScientificSourceReceipt
    functionalReceipt : Fly.ScientificSourceReceipt
    motorEffectorReceipt : Fly.ScientificSourceReceipt

    State : Set
    Observation : Set
    Candidate : Set
    Receipt : Set

    candidateFromObservation : Observation → Candidate
    promotionAdmissible : Observation → Candidate → Receipt → Set
    promotedState : Candidate → State

    stateToBehaviourObservation : State → Observation

    sharedUpstreamEvidenceMustRemainDependent : Bool
    sharedUpstreamEvidenceMustRemainDependentIsTrue :
      sharedUpstreamEvidenceMustRemainDependent ≡ true

    interpretationReading : String

open GovernedFlyExperiment public

------------------------------------------------------------------------
-- Intervention language: passive correlation does not close causal/semantic
-- questions.  Drosophila perturbations may refine latent alternatives if the
-- experiment is explicitly admissible and separating.
------------------------------------------------------------------------

FlyExperimentLanguage : Set → Set₁
FlyExperimentLanguage = Lexic.AnimalExperimentLanguage

flySeparatingExperimentRefutesEquivalence =
  Lexic.animalAdmissibleSeparatingExperimentRefutesSemanticEquivalence

------------------------------------------------------------------------
-- Provenance independence is inherited from Animalexic: modality labels do
-- not make evidence independent when upstream acquisition/registration roots
-- are shared.
------------------------------------------------------------------------

FlyProvenanceSystem : Set → Set₁
FlyProvenanceSystem = Lexic.AnimalProvenanceSystem

flySharedRootRefutesIndependence =
  Lexic.animalSharedUpstreamRootRefutesIndependence

canonicalDrosophilaAnimalexicBoundaries : List DrosophilaAnimalexicBoundary
canonicalDrosophilaAnimalexicBoundaries =
  noNeuralStateEqualsBehaviourMotif
  ∷ noBehaviourMotifEqualsSemanticMeaning
  ∷ noFunctionalCorrelationEqualsCommunicativeAct
  ∷ noSingleModalityPromotion
  ∷ noCandidateEqualsPromotedState
  ∷ noCrossSpeciesSemanticTransferWithoutReceipt
  ∷ noSharedSourceCountsAsIndependentEvidence
  ∷ []
