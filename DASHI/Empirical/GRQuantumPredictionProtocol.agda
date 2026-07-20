module DASHI.Empirical.GRQuantumPredictionProtocol where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Empirical.GRQuantumObservableCalibration as Observable

data ⊥ : Set where

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Quantitative prediction contract.
--
-- A prediction must be locked before the held-out observation, use the same
-- calibrated observable as the correspondence layer, and include an outcome
-- that rejects DASHI rather than merely preferring it over one baseline.

record ScaledQuantity : Set where
  constructor scaled-quantity
  field
    numerator : Nat
    denominator : Nat
    decimalExponent : Nat
    unit : Observable.PhysicalUnit
open ScaledQuantity public

record PredictionProvenance : Set where
  constructor prediction-provenance
  field
    theoryRevision : String
    parameterManifestHash : String
    derivationArtifactHash : String
    preregistrationIdentifier : String
    preregistrationTimestamp : String
    blindingOrHoldoutPolicy : String
    competingModels : List String
open PredictionProvenance public

record QuantitativeFalsifiablePrediction : Set₁ where
  field
    ExperimentalSetup : Set
    Observation : Set
    TestStatistic : Set

    setup : ExperimentalSetup
    observableName : String
    observableUnit : Observable.PhysicalUnit

    dashiCentralValue : ScaledQuantity
    dashiUncertainty : ScaledQuantity
    nullCentralValue : ScaledQuantity
    nullUncertainty : ScaledQuantity
    minimumDistinguishableSeparation : ScaledQuantity
    centralPredictionsDiffer : dashiCentralValue ≢ nullCentralValue

    statistic : Observation → TestStatistic
    DASHIAcceptanceRegion : TestStatistic → Set
    NullAcceptanceRegion : TestStatistic → Set
    rejectDASHI : Observation → Bool
    rejectNull : Observation → Bool

    rejectionCriterionExplicit : Set
    rejectionCriterionExplicitProof : rejectionCriterionExplicit
    outcomeSpaceCanRejectDASHI : Set
    outcomeSpaceCanRejectDASHIProof : outcomeSpaceCanRejectDASHI
    statisticalPowerOrSensitivityDeclared : Set
    statisticalPowerOrSensitivityDeclaredProof :
      statisticalPowerOrSensitivityDeclared
    systematicsBudgetDeclared : Set
    systematicsBudgetDeclaredProof : systematicsBudgetDeclared
    observableUsesCalibrationProgramme : Set
    observableUsesCalibrationProgrammeProof :
      observableUsesCalibrationProgramme
    noPostHocParameterAdjustment : Set
    noPostHocParameterAdjustmentProof : noPostHocParameterAdjustment

    provenance : PredictionProvenance
open QuantitativeFalsifiablePrediction public

record GRQuantumPredictionSuite : Set₁ where
  field
    primaryPrediction : QuantitativeFalsifiablePrediction
    calibrationControl : QuantitativeFalsifiablePrediction
    referenceTheoryControl : QuantitativeFalsifiablePrediction

    primaryUsesHeldOutObservation : Set
    primaryUsesHeldOutObservationProof : primaryUsesHeldOutObservation
    allAnalysisChoicesFrozen : Set
    allAnalysisChoicesFrozenProof : allAnalysisChoicesFrozen
    nullResultPublished : Set
    nullResultPublishedProof : nullResultPublished
    adverseResultPublished : Set
    adverseResultPublishedProof : adverseResultPublished
open GRQuantumPredictionSuite public

------------------------------------------------------------------------
-- Request packet only.  It records the source modules that a future concrete
-- prediction must consume, but deliberately supplies no invented physical value.

record PredictionRequestPacket : Set where
  constructor prediction-request-packet
  field
    observableProgramme : String
    continuumTarget : String
    quantumTarget : String
    sourceEquationTarget : String
    benchmarkProtocol : String
    predictionSelected : Bool
    predictionSelectedIsFalse : predictionSelected ≡ false
    reason : String
open PredictionRequestPacket public

canonicalPredictionRequestPacket : PredictionRequestPacket
canonicalPredictionRequestPacket =
  prediction-request-packet
    "DASHI.Empirical.GRQuantumObservableCalibration"
    "DASHI.Physics.DiscreteContinuumKernelTargets"
    "DASHI.Physics.Closure.PhysicalRealComplexRGCFTRoute"
    "DASHI.Physics.Closure.PropositionEinsteinBridge"
    "DASHI.Empirical.GRQuantumBenchmarkProtocol"
    false
    refl
    "No quantitative physical deviation is derived by the current finite/model stack; selecting a number without a continuum and calibration derivation would be fabrication."

record PredictionBoundary : Set where
  constructor prediction-boundary
  field
    predictionProtocolImplemented : Bool
    predictionProtocolImplementedIsTrue :
      predictionProtocolImplemented ≡ true
    quantitativePredictionDerived : Bool
    quantitativePredictionDerivedIsFalse :
      quantitativePredictionDerived ≡ false
    postHocPredictionAllowed : Bool
    postHocPredictionAllowedIsFalse : postHocPredictionAllowed ≡ false
open PredictionBoundary public

canonicalPredictionBoundary : PredictionBoundary
canonicalPredictionBoundary =
  prediction-boundary true refl false refl false refl
