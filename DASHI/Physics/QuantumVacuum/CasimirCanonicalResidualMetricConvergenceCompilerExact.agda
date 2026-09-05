module DASHI.Physics.QuantumVacuum.CasimirCanonicalResidualMetricConvergenceCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
import Data.Nat.Properties as NatP

import Real as Bishop
import Sequence as BishopSequence

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.CasimirResidualCauchyToLimitExact as Residual
import DASHI.Physics.QuantumVacuum.CasimirResidualConvergenceRouteBidiExact as Route
import DASHI.Physics.QuantumVacuum.CasimirRegulatorMetricTailReceiptExact as Tail
import DASHI.Physics.QuantumVacuum.CasimirBishopCanonicalResidualMetricTailExact as Canonical

------------------------------------------------------------------------
-- CANONICAL POINTWISE METRIC CONVERGENCE -> BISHOP CONVERGENCE
------------------------------------------------------------------------

canonicalPointwiseToBishopConvergence :
  ∀ {residualAt candidate} →
  Metric.PointwiseMetricConvergence
    (Canonical.bishopResidualMetricProblem residualAt candidate) →
  BishopSequence._ConvergesTo_ residualAt candidate
canonicalPointwiseToBishopConvergence M =
  BishopSequence.con* λ
    { (suc precision) →
      let
        thresholdIndex = Metric.threshold M tt precision
      in
      thresholdIndex , λ n nAboveSuccessorThreshold →
        Metric.tailClose M
          tt
          precision
          tt
          n
          (NatP.≤-trans
            (NatP.n≤1+n thresholdIndex)
            nAboveSuccessorThreshold)
    }

------------------------------------------------------------------------
-- One canonical input: literal residual, literal candidate, actual tail proof.
------------------------------------------------------------------------

record CanonicalResidualTailInput : Set₁ where
  field
    residualAt : Nat → Bishop.ℝ
    candidate : Bishop.ℝ

    tail : Tail.ProofBearingMetricTail
      (Canonical.bishopResidualMetricProblem residualAt candidate)

    reading : String

open CanonicalResidualTailInput public

asDirectResidualMetricLimit :
  CanonicalResidualTailInput →
  Route.DirectResidualMetricLimit
asDirectResidualMetricLimit I = record
  { Route.residualAt = residualAt I
  ; Route.sequence = residualAt I
  ; Route.sequenceIsResidual = λ n → Spine.≈-refl Residual.Real
  ; Route.metricProblem =
      Canonical.bishopResidualMetricProblem (residualAt I) (candidate I)
  ; Route.metricConvergence = Tail.asPointwiseMetricConvergence (tail I)
  ; Route.ParameterWitness = ⊤
  ; Route.parameterWitness = tt
  ; Route.candidate = candidate I
  ; Route.sameLiteralResidualTrajectory = ⊤
  ; Route.sameCandidateLimit = ⊤
  ; Route.directMetricTailImpliesBishopConvergence =
      canonicalPointwiseToBishopConvergence
  ; Route.reading = reading I
  }

compileCanonicalResidualLimit :
  CanonicalResidualTailInput →
  Route.ResidualLimitResult
compileCanonicalResidualLimit I =
  Route.compileResidualLimit
    (Route.viaDirectMetricTail (asDirectResidualMetricLimit I))

canonicalResidualConverges :
  (I : CanonicalResidualTailInput) →
  BishopSequence._ConvergesTo_ (residualAt I) (candidate I)
canonicalResidualConverges I =
  canonicalPointwiseToBishopConvergence
    (Tail.asPointwiseMetricConvergence (tail I))

------------------------------------------------------------------------
-- BIDI pruning.
------------------------------------------------------------------------

record ReverseCanonicalResidualLimitObligations : Set where
  field
    oneOverSuccessorTailTheorem : Set
    presentationIndependence : Set
    reading : String

open ReverseCanonicalResidualLimitObligations public

data SeparateResidualTrajectoryWeldRequired : Set where
data SeparateResidualCandidateWeldRequired : Set where
data SeparateMetricToBishopTransportRequired : Set where

definitionalTrajectoryPrunesWeld :
  SeparateResidualTrajectoryWeldRequired → ⊥
definitionalTrajectoryPrunesWeld ()

definitionalCandidatePrunesWeld :
  SeparateResidualCandidateWeldRequired → ⊥
definitionalCandidatePrunesWeld ()

canonicalMetricPrunesTransport :
  SeparateMetricToBishopTransportRequired → ⊥
canonicalMetricPrunesTransport ()

record Status : Set where
  field
    literalResidualMetricFamilyOwned : Bool
    literalCandidateOwnedByConstruction : Bool
    pointwiseMetricToBishopCompilerOwned : Bool
    directResidualLimitCompilerOwned : Bool
    onlyConcreteTailEstimateRemains : Bool

    literalResidualMetricFamilyOwnedIsTrue : literalResidualMetricFamilyOwned ≡ true
    literalCandidateOwnedByConstructionIsTrue : literalCandidateOwnedByConstruction ≡ true
    pointwiseMetricToBishopCompilerOwnedIsTrue : pointwiseMetricToBishopCompilerOwned ≡ true
    directResidualLimitCompilerOwnedIsTrue : directResidualLimitCompilerOwned ≡ true
    onlyConcreteTailEstimateRemainsIsTrue : onlyConcreteTailEstimateRemains ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { literalResidualMetricFamilyOwned = true
  ; literalCandidateOwnedByConstruction = true
  ; pointwiseMetricToBishopCompilerOwned = true
  ; directResidualLimitCompilerOwned = true
  ; onlyConcreteTailEstimateRemains = true
  ; literalResidualMetricFamilyOwnedIsTrue = refl
  ; literalCandidateOwnedByConstructionIsTrue = refl
  ; pointwiseMetricToBishopCompilerOwnedIsTrue = refl
  ; directResidualLimitCompilerOwnedIsTrue = refl
  ; onlyConcreteTailEstimateRemainsIsTrue = refl
  }
