module DASHI.Empirical.GRQuantumCorrespondenceBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Scientific correspondence boundary for the formal unification stack.
--
-- Formal closure under selected axioms is not empirical confirmation.  This
-- record requires explicit decode maps, recovered limits, benchmark receipts,
-- a falsifiable prediction, and independent review before physical promotion.

record ObservableCorrespondence : Set₁ where
  field
    FormalObservable : Set
    MeasuredObservable : Set
    decode : FormalObservable → MeasuredObservable
    calibrationData : Set
    calibrationProof : calibrationData
    unitsAndNormalizationFixed : Set
    unitsAndNormalizationProof : unitsAndNormalizationFixed
open ObservableCorrespondence public

record KnownLimitRecovery : Set₁ where
  field
    FormalRegime : Set
    ReferenceTheoryResult : Set
    DASHIResult : Set
    lowEnergyOrWeakFieldLimit : Set
    lowEnergyOrWeakFieldLimitProof : lowEnergyOrWeakFieldLimit
    agreement : DASHIResult → ReferenceTheoryResult → Set
    agreementProof : (dashi : DASHIResult) →
                     (reference : ReferenceTheoryResult) →
                     agreement dashi reference
open KnownLimitRecovery public

record NumericalBenchmarkReceipt : Set₁ where
  field
    BenchmarkInput : Set
    DASHIOutput : Set
    ReferenceOutput : Set
    ErrorMeasure : Set
    runtimeMeasure : Set
    memoryMeasure : Set
    matchedQuality : Set
    matchedQualityProof : matchedQuality
    reproducibleArtifact : Set
    reproducibleArtifactProof : reproducibleArtifact
open NumericalBenchmarkReceipt public

record FalsifiablePrediction : Set₁ where
  field
    ExperimentalSetup : Set
    PredictedObservable : Set
    nullOrReferencePrediction : PredictedObservable
    dashiPrediction : PredictedObservable
    distinguishable : Set
    distinguishableProof : distinguishable
    rejectionCriterion : Set
    rejectionCriterionExplicit : rejectionCriterion
open FalsifiablePrediction public

record IndependentReviewReceipt : Set₁ where
  field
    mathematicalReview : Set
    mathematicalReviewProof : mathematicalReview
    physicsReview : Set
    physicsReviewProof : physicsReview
    replication : Set
    replicationProof : replication
    conflictsDisclosed : Set
    conflictsDisclosedProof : conflictsDisclosed
open IndependentReviewReceipt public

record PhysicalGRQuantumCorrespondence : Set₁ where
  field
    observables : ObservableCorrespondence
    knownLimits : KnownLimitRecovery
    numericalBenchmark : NumericalBenchmarkReceipt
    prediction : FalsifiablePrediction
    independentReview : IndependentReviewReceipt
open PhysicalGRQuantumCorrespondence public

------------------------------------------------------------------------
-- Ledger only: no canonical physical correspondence is constructed.


data CorrespondenceGate : Set where
  observableMapGate : CorrespondenceGate
  knownLimitGate : CorrespondenceGate
  numericalBenchmarkGate : CorrespondenceGate
  falsifiablePredictionGate : CorrespondenceGate
  independentReviewGate : CorrespondenceGate

canonicalCorrespondenceGates : List CorrespondenceGate
canonicalCorrespondenceGates =
  observableMapGate
  ∷ knownLimitGate
  ∷ numericalBenchmarkGate
  ∷ falsifiablePredictionGate
  ∷ independentReviewGate
  ∷ []

correspondenceGateText : CorrespondenceGate → String
correspondenceGateText observableMapGate =
  "Map formal states/operators to measured quantities with units and calibration."
correspondenceGateText knownLimitGate =
  "Recover accepted GR, quantum, and field-theory limits in stated regimes."
correspondenceGateText numericalBenchmarkGate =
  "Compare errors, runtime, and memory against matched-quality reference solvers."
correspondenceGateText falsifiablePredictionGate =
  "State a quantitative prediction distinguishable from the null/reference model."
correspondenceGateText independentReviewGate =
  "Obtain independent proof review, physics review, and replication."

physicalPromotionRequiresCorrespondence :
  PhysicalGRQuantumCorrespondence → PhysicalGRQuantumCorrespondence
physicalPromotionRequiresCorrespondence receipt = receipt
