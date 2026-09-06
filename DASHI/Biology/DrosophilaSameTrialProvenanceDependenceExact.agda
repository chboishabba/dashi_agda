module DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalexicDrosophilaEmbodiedBridge as AX
import DASHI.Biology.DrosophilaBenchmarkReceiptProtocol as Receipt

------------------------------------------------------------------------
-- Same-trial provenance and evidence dependence.
--
-- Multimodal agreement is not promoted to independent replication when two
-- observations share an animal, trial, registration, preprocessing, or model
-- root.  Dependence is represented explicitly and can be consumed by benchmark
-- aggregation rather than silently assuming IID evidence.
------------------------------------------------------------------------

data ProvenanceRootKind : Set where
  datasetRoot : ProvenanceRootKind
  animalRoot : ProvenanceRootKind
  trialRoot : ProvenanceRootKind
  acquisitionRoot : ProvenanceRootKind
  registrationRoot : ProvenanceRootKind
  preprocessingRoot : ProvenanceRootKind
  predictorRoot : ProvenanceRootKind
  observerProtocolRoot : ProvenanceRootKind

data EvidenceRelation : Set where
  sameTrialCorroboration : EvidenceRelation
  crossTrialReplication : EvidenceRelation
  crossAnimalReplication : EvidenceRelation
  crossDatasetReplication : EvidenceRelation
  sharedPipelineCorroboration : EvidenceRelation
  independenceUndetermined : EvidenceRelation

data DependenceBoundary : Set where
  noDistinctModalityImpliesIndependence : DependenceBoundary
  noSameTrialCountsAsIndependentReplication : DependenceBoundary
  noSameRegistrationCountsAsIndependentReplication : DependenceBoundary
  noSharedPreprocessingCountsAsIndependentReplication : DependenceBoundary
  noRepeatedMetricCountsAsNewEvidence : DependenceBoundary
  noUnknownProvenancePromotesIndependence : DependenceBoundary

record ProvenanceNode : Set where
  field
    nodeID : String
    rootKind : ProvenanceRootKind
    stableReference : String

open ProvenanceNode public

record ProvenanceGraph : Set₁ where
  field
    Artifact : Set
    Root : Set
    rootsOf : Artifact → List Root
    sharedRoot : Artifact → Artifact → Set
    sharedRootSound :
      ∀ left right → sharedRoot left right → Set

open ProvenanceGraph public

record SameTrialObservationBundle : Set₁ where
  field
    StructuralArtifact : Set
    FunctionalArtifact : Set
    BodyArtifact : Set
    BehaviourArtifact : Set
    RegistrationArtifact : Set
    Trial : Set
    Animal : Set

    structural : StructuralArtifact
    functional : FunctionalArtifact
    body : BodyArtifact
    behaviour : BehaviourArtifact
    registration : RegistrationArtifact
    trial : Trial
    animal : Animal

    structuralReceipt : Receipt.ArtifactReceipt
    functionalReceipt : Receipt.ArtifactReceipt
    bodyReceipt : Receipt.ArtifactReceipt
    behaviourReceipt : Receipt.ArtifactReceipt

    sameTrialPinned : Bool
    sameTrialPinnedIsTrue : sameTrialPinned ≡ true
    sameAnimalPinned : Bool
    sameAnimalPinnedIsTrue : sameAnimalPinned ≡ true

open SameTrialObservationBundle public

record EvidenceDependenceAssessment : Set where
  field
    relation : EvidenceRelation
    sharedAnimalRoot : Bool
    sharedTrialRoot : Bool
    sharedRegistrationRoot : Bool
    sharedPreprocessingRoot : Bool
    independentReplicationClaim : Bool

    sameTrialBlocksIndependentReplication :
      sharedTrialRoot ≡ true → independentReplicationClaim ≡ false

    sameAnimalBlocksCrossAnimalReplication :
      sharedAnimalRoot ≡ true →
      relation ≡ crossAnimalReplication →
      false ≡ true

open EvidenceDependenceAssessment public

record DependenceAwareResidualAggregation : Set₁ where
  field
    Residual : Set
    EvidenceUnit : Set
    DependencyClass : Set
    residualOf : EvidenceUnit → Residual
    dependencyClass : EvidenceUnit → DependencyClass
    aggregateWithinClass : List Residual → Residual
    aggregateAcrossIndependentClasses : List Residual → Residual
    dependenceReading : String

open DependenceAwareResidualAggregation public

record FlyTrialEvidenceSurface : Set₁ where
  field
    Bundle : Set
    Candidate : Set
    CanonicalState : Set
    bundleCandidate : Bundle → Candidate
    promote : Candidate → CanonicalState
    promotionRequiresReceipt : Bool
    promotionRequiresReceiptIsTrue : promotionRequiresReceipt ≡ true
    independenceRequiresProvenanceClosure : Bool
    independenceRequiresProvenanceClosureIsTrue :
      independenceRequiresProvenanceClosure ≡ true

open FlyTrialEvidenceSurface public

canonicalDependenceBoundaries : List DependenceBoundary
canonicalDependenceBoundaries =
  noDistinctModalityImpliesIndependence
  ∷ noSameTrialCountsAsIndependentReplication
  ∷ noSameRegistrationCountsAsIndependentReplication
  ∷ noSharedPreprocessingCountsAsIndependentReplication
  ∷ noRepeatedMetricCountsAsNewEvidence
  ∷ noUnknownProvenancePromotesIndependence
  ∷ []
