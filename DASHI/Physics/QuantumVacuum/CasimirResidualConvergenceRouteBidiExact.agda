module DASHI.Physics.QuantumVacuum.CasimirResidualConvergenceRouteBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.CasimirResidualCauchyToLimitExact as Cauchy
import DASHI.Physics.QuantumVacuum.CasimirResidualSummableIncrementBidiExact as Increment

------------------------------------------------------------------------
-- CASIMIR RESIDUAL CONVERGENCE: TWO LEGITIMATE ROUTES
--
-- Route A: successive residual increments -> summable tail -> Bishop Cauchy ->
--          completeness -> limit.
-- Route B: a direct regulator epsilon-tail estimate to a selected candidate ->
--          transport that metric convergence directly to Bishop convergence.
--
-- These are alternatives.  A proof should not be forced to establish both.
------------------------------------------------------------------------

record DirectResidualMetricLimit : Set₁ where
  field
    residualAt : Nat → Spine.Carrier Cauchy.Real
    sequence : Spine.Sequence Cauchy.Real
    sequenceIsResidual : ∀ n →
      Spine._≈_ Cauchy.Real
        (Spine.sequenceAt Cauchy.Real sequence n)
        (residualAt n)

    metricProblem : Metric.ParameterisedMetricLimitProblem
    metricConvergence : Metric.PointwiseMetricConvergence metricProblem

    ParameterWitness : Set
    parameterWitness : ParameterWitness
    candidate : Spine.Carrier Cauchy.Real

    sameLiteralResidualTrajectory : Set
    sameCandidateLimit : Set

    directMetricTailImpliesBishopConvergence :
      Metric.PointwiseMetricConvergence metricProblem →
      Spine.ConvergesTo Cauchy.Real sequence candidate

    reading : String

open DirectResidualMetricLimit public

directResidualConverges :
  (D : DirectResidualMetricLimit) →
  Spine.ConvergesTo Cauchy.Real (sequence D) (candidate D)
directResidualConverges D =
  directMetricTailImpliesBishopConvergence D (metricConvergence D)

record DirectResidualLimitReceipt : Set₁ where
  field
    direct : DirectResidualMetricLimit
    limit : Spine.Carrier Cauchy.Real
    limitIsCandidate : Spine._≈_ Cauchy.Real limit (candidate direct)
    converges : Spine.ConvergesTo Cauchy.Real (sequence direct) limit

open DirectResidualLimitReceipt public

compileDirectResidualLimit :
  (D : DirectResidualMetricLimit) →
  DirectResidualLimitReceipt
compileDirectResidualLimit D = record
  { direct = D
  ; limit = candidate D
  ; limitIsCandidate = Spine.≈-refl Cauchy.Real
  ; converges = directResidualConverges D
  }

------------------------------------------------------------------------
-- Disjunctive convergence certificate.
------------------------------------------------------------------------

data ResidualConvergenceRoute : Set₁ where
  viaSummableIncrements :
    Increment.CasimirResidualSummableIncrement →
    ResidualConvergenceRoute
  viaDirectMetricTail :
    DirectResidualMetricLimit →
    ResidualConvergenceRoute

record ResidualLimitResult : Set₁ where
  field
    limit : Spine.Carrier Cauchy.Real
    SequenceUsed : Spine.Sequence Cauchy.Real
    converges : Spine.ConvergesTo Cauchy.Real SequenceUsed limit
    reading : String

open ResidualLimitResult public

compileResidualLimit : ResidualConvergenceRoute → ResidualLimitResult
compileResidualLimit (viaSummableIncrements increments) =
  let
    residual = Increment.compileResidualRegulatorSequence increments
  in record
    { limit = Cauchy.residualLimit residual
    ; SequenceUsed = Cauchy.sequence residual
    ; converges = Cauchy.residualConverges residual
    ; reading = "Residual limit compiled through summable successive increments and Bishop completeness."
    }
compileResidualLimit (viaDirectMetricTail direct) = record
  { limit = candidate direct
  ; SequenceUsed = sequence direct
  ; converges = directResidualConverges direct
  ; reading = "Residual limit compiled directly from a regulator epsilon-tail estimate to the same Bishop candidate."
  }

record ReverseResidualConvergenceObligations : Set where
  field
    sameLiteralPostCancellationResidual : Set
    oneOfTwoRoutesRequired : Set
    incrementRouteRequiresSummableIncrementMajorant : Set
    directRouteRequiresCandidateTailEstimate : Set
    bishopMetricTransportForChosenRoute : Set

open ReverseResidualConvergenceObligations public

data BothConvergenceRoutesAreRequired : Set where

data DirectTailEstimateAutomaticallyIsIncrementEstimate : Set where

data IncrementEstimateAutomaticallyIdentifiesDirectCandidate : Set where

notBothRoutesRequired : BothConvergenceRoutesAreRequired → ⊥
notBothRoutesRequired ()

noDirectToIncrementLeak : DirectTailEstimateAutomaticallyIsIncrementEstimate → ⊥
noDirectToIncrementLeak ()

noIncrementToDirectCandidateLeak : IncrementEstimateAutomaticallyIdentifiesDirectCandidate → ⊥
noIncrementToDirectCandidateLeak ()

record Status : Set where
  field
    summableIncrementRouteOwned : Bool
    directMetricTailRouteOwned : Bool
    disjunctiveConvergenceCompilerOwned : Bool
    concreteIncrementMajorantClosed : Bool
    concreteDirectTailEstimateClosed : Bool

    summableIncrementRouteOwnedIsTrue : summableIncrementRouteOwned ≡ true
    directMetricTailRouteOwnedIsTrue : directMetricTailRouteOwned ≡ true
    disjunctiveConvergenceCompilerOwnedIsTrue : disjunctiveConvergenceCompilerOwned ≡ true
    concreteIncrementMajorantClosedIsFalse : concreteIncrementMajorantClosed ≡ false
    concreteDirectTailEstimateClosedIsFalse : concreteDirectTailEstimateClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { summableIncrementRouteOwned = true
  ; directMetricTailRouteOwned = true
  ; disjunctiveConvergenceCompilerOwned = true
  ; concreteIncrementMajorantClosed = false
  ; concreteDirectTailEstimateClosed = false
  ; summableIncrementRouteOwnedIsTrue = refl
  ; directMetricTailRouteOwnedIsTrue = refl
  ; disjunctiveConvergenceCompilerOwnedIsTrue = refl
  ; concreteIncrementMajorantClosedIsFalse = refl
  ; concreteDirectTailEstimateClosedIsFalse = refl
  }
