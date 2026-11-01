module DASHI.Empirical.GRQuantumEmpiricalValidationProgramme where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Empirical.GRQuantumCorrespondenceBoundary as Legacy
import DASHI.Empirical.GRQuantumObservableCalibration as Observable
import DASHI.Empirical.GRQuantumKnownLimitRecovery as Limits
import DASHI.Empirical.GRQuantumBenchmarkProtocol as Benchmarks
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Empirical.GRQuantumIndependentReview as Review

------------------------------------------------------------------------
-- Strict empirical completion.
--
-- The legacy correspondence surface remains available for compatibility.  This
-- record is the physical-promotion authority: it expands every legacy slot into
-- a domain-specific, auditable receipt and requires cross-lane coherence.

record StrictPhysicalGRQuantumCorrespondence : Set₁ where
  field
    legacySurface : Legacy.PhysicalGRQuantumCorrespondence
    observableCalibration : Observable.GRQuantumObservableCalibration
    acceptedLimits : Limits.AcceptedGRQFTLimitSuite
    matchedQualityBenchmarks : Benchmarks.GRQuantumBenchmarkSuite
    falsifiablePrediction : Prediction.GRQuantumPredictionSuite
    independentReviewAndReplication :
      Review.IndependentGRQuantumReviewPackage

    legacyObservableSurfaceAgrees : Set
    legacyObservableSurfaceAgreesProof : legacyObservableSurfaceAgrees
    legacyLimitSurfaceAgrees : Set
    legacyLimitSurfaceAgreesProof : legacyLimitSurfaceAgrees
    legacyBenchmarkSurfaceAgrees : Set
    legacyBenchmarkSurfaceAgreesProof : legacyBenchmarkSurfaceAgrees
    legacyPredictionSurfaceAgrees : Set
    legacyPredictionSurfaceAgreesProof : legacyPredictionSurfaceAgrees
    legacyReviewSurfaceAgrees : Set
    legacyReviewSurfaceAgreesProof : legacyReviewSurfaceAgrees

    oneTheoryRevisionAcrossAllReceipts : Set
    oneTheoryRevisionAcrossAllReceiptsProof :
      oneTheoryRevisionAcrossAllReceipts
    oneParameterManifestAcrossAllReceipts : Set
    oneParameterManifestAcrossAllReceiptsProof :
      oneParameterManifestAcrossAllReceipts
    calibrationLimitBenchmarkPredictionObservableCoherence : Set
    calibrationLimitBenchmarkPredictionObservableCoherenceProof :
      calibrationLimitBenchmarkPredictionObservableCoherence
    noCircularUseOfTargetClaim : Set
    noCircularUseOfTargetClaimProof : noCircularUseOfTargetClaim
    adverseAndNullResultsRetained : Set
    adverseAndNullResultsRetainedProof : adverseAndNullResultsRetained
open StrictPhysicalGRQuantumCorrespondence public

data PhysicalGRQuantumEmpiricalPromotion : Set₁ where
  promotePhysicalGRQuantum :
    StrictPhysicalGRQuantumCorrespondence →
    PhysicalGRQuantumEmpiricalPromotion

------------------------------------------------------------------------
-- Current repository readiness bundle.
--
-- This is constructible because it contains protocol boundaries and exact finite
-- adapters only.  It cannot be converted into strict physical correspondence.

record GRQuantumEmpiricalReadiness : Set where
  constructor gr-quantum-empirical-readiness
  field
    observableBoundary : Observable.ObservableCalibrationBoundary
    limitBoundary : Limits.KnownLimitBoundary
    benchmarkBoundary : Benchmarks.BenchmarkBoundary
    predictionBoundary : Prediction.PredictionBoundary
    reviewBoundary : Review.IndependentReviewBoundary

    observableReferences : Observable.ExistingObservableReferenceMap
    finiteLimitAdapters : Limits.ExistingFiniteLimitAdapters
    benchmarkReferences : Benchmarks.ExistingBenchmarkReferences
    predictionRequest : Prediction.PredictionRequestPacket
    reviewRequest : Review.ReviewRequestPacket

    additionalRepositoryReferences : List String
    physicalPromotionAvailable : Bool
    physicalPromotionAvailableIsFalse : physicalPromotionAvailable ≡ false
    scope : String
open GRQuantumEmpiricalReadiness public

canonicalGRQuantumEmpiricalReadiness : GRQuantumEmpiricalReadiness
canonicalGRQuantumEmpiricalReadiness =
  gr-quantum-empirical-readiness
    Observable.canonicalObservableCalibrationBoundary
    Limits.canonicalKnownLimitBoundary
    Benchmarks.canonicalBenchmarkBoundary
    Prediction.canonicalPredictionBoundary
    Review.canonicalIndependentReviewBoundary
    Observable.canonicalExistingObservableReferenceMap
    Limits.canonicalExistingFiniteLimitAdapters
    Benchmarks.canonicalExistingBenchmarkReferences
    Prediction.canonicalPredictionRequestPacket
    Review.canonicalReviewRequestPacket
    ("DASHI.Physics.DiscreteContinuumKernelTargets"
      ∷ "DASHI.Physics.Closure.PhysicalRGCFTEmpiricalAuthority"
      ∷ "DASHI.Environment.ValidationGovernance"
      ∷ "DASHI.Environment.SurrogateCalibration"
      ∷ "scripts/validate_multiscale_flagship_receipt.py"
      ∷ [])
    false
    refl
    "all seven protocol lanes are implemented and cross-referenced; measured completion, a derived prediction, independent reviews and replication remain external obligations"

strictEmpiricalAuthorityRequired :
  StrictPhysicalGRQuantumCorrespondence →
  StrictPhysicalGRQuantumCorrespondence
strictEmpiricalAuthorityRequired authority = authority
