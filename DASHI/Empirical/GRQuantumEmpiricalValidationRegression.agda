module DASHI.Empirical.GRQuantumEmpiricalValidationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Empirical.GRQuantumObservableCalibration as Observable
import DASHI.Empirical.GRQuantumKnownLimitRecovery as Limits
import DASHI.Empirical.GRQuantumBenchmarkProtocol as Benchmark
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Empirical.GRQuantumIndependentReview as Review
import DASHI.Empirical.GRQuantumEmpiricalValidationProgramme as Programme

observableProgrammePresent :
  Observable.ObservableCalibrationBoundary.typedProgrammeImplemented
    Observable.canonicalObservableCalibrationBoundary
  ≡ true
observableProgrammePresent =
  Observable.ObservableCalibrationBoundary.typedProgrammeImplementedIsTrue
    Observable.canonicalObservableCalibrationBoundary

measuredCalibrationStillOpen :
  Observable.ObservableCalibrationBoundary.measuredCalibrationCompleted
    Observable.canonicalObservableCalibrationBoundary
  ≡ false
measuredCalibrationStillOpen =
  Observable.ObservableCalibrationBoundary.measuredCalibrationCompletedIsFalse
    Observable.canonicalObservableCalibrationBoundary

acceptedLimitSuiteStillOpen :
  Limits.KnownLimitBoundary.acceptedPhysicalLimitSuiteCompleted
    Limits.canonicalKnownLimitBoundary
  ≡ false
acceptedLimitSuiteStillOpen =
  Limits.KnownLimitBoundary.acceptedPhysicalLimitSuiteCompletedIsFalse
    Limits.canonicalKnownLimitBoundary

matchedBenchmarkSuiteStillOpen :
  Benchmark.BenchmarkBoundary.physicalMatchedQualitySuiteCompleted
    Benchmark.canonicalBenchmarkBoundary
  ≡ false
matchedBenchmarkSuiteStillOpen =
  Benchmark.BenchmarkBoundary.physicalMatchedQualitySuiteCompletedIsFalse
    Benchmark.canonicalBenchmarkBoundary

quantitativePredictionStillOpen :
  Prediction.PredictionBoundary.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
quantitativePredictionStillOpen =
  Prediction.PredictionBoundary.quantitativePredictionDerivedIsFalse
    Prediction.canonicalPredictionBoundary

mathematicsReviewStillOpen :
  Review.IndependentReviewBoundary.independentMathematicsReviewObtained
    Review.canonicalIndependentReviewBoundary
  ≡ false
mathematicsReviewStillOpen =
  Review.IndependentReviewBoundary.independentMathematicsReviewObtainedIsFalse
    Review.canonicalIndependentReviewBoundary

physicsReviewStillOpen :
  Review.IndependentReviewBoundary.independentPhysicsReviewObtained
    Review.canonicalIndependentReviewBoundary
  ≡ false
physicsReviewStillOpen =
  Review.IndependentReviewBoundary.independentPhysicsReviewObtainedIsFalse
    Review.canonicalIndependentReviewBoundary

replicationStillOpen :
  Review.IndependentReviewBoundary.independentReplicationObtained
    Review.canonicalIndependentReviewBoundary
  ≡ false
replicationStillOpen =
  Review.IndependentReviewBoundary.independentReplicationObtainedIsFalse
    Review.canonicalIndependentReviewBoundary

strictPhysicalPromotionStillClosed :
  Programme.GRQuantumEmpiricalReadiness.physicalPromotionAvailable
    Programme.canonicalGRQuantumEmpiricalReadiness
  ≡ false
strictPhysicalPromotionStillClosed =
  Programme.GRQuantumEmpiricalReadiness.physicalPromotionAvailableIsFalse
    Programme.canonicalGRQuantumEmpiricalReadiness
