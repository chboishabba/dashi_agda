module DASHI.Physics.QuantumVacuum.CasimirRegulatorTailDirectConvergenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse
import DASHI.Physics.QuantumVacuum.CasimirRegulatorDominatedTailCutsetExact as Tail
import DASHI.Physics.QuantumVacuum.CasimirResidualCauchyToLimitExact as Residual
import DASHI.Physics.QuantumVacuum.CasimirResidualConvergenceRouteBidiExact as Route

------------------------------------------------------------------------
-- EXISTING REGULATOR TAIL CUTSET -> DIRECT RESIDUAL LIMIT ROUTE
--
-- `CasimirRegulatorDominatedTailCutsetExact` already records a metric problem,
-- threshold formula and tail-estimate obligation.  This owner makes those data
-- productive: once the tail estimate is realized as pointwise metric
-- convergence on the same residual trajectory/candidate, the new disjunctive
-- residual compiler bypasses the independent summable-increment route.
------------------------------------------------------------------------

record RegulatorTailPointwiseRealisation
    {kernel : Casimir.CasimirScalarModel}
    {F : Transverse.CasimirTransverseMeasureFamily kernel}
    (T : Tail.RegulatorTailEstimate) : Set₁ where
  field
    tailEstimateEvidence : Tail.tailEstimate T

    pointwiseFromTailEstimate :
      Tail.tailEstimate T →
      Metric.PointwiseMetricConvergence (Tail.metricProblem T)

    presentationIndependentEvidence : Tail.presentationIndependentTail T
    reading : String

open RegulatorTailPointwiseRealisation public

compilePointwiseMetricConvergence :
  ∀ {kernel F}
    {T : Tail.RegulatorTailEstimate} →
  RegulatorTailPointwiseRealisation {kernel} {F} T →
  Metric.PointwiseMetricConvergence (Tail.metricProblem T)
compilePointwiseMetricConvergence R =
  pointwiseFromTailEstimate R (tailEstimateEvidence R)

record RegulatorTailResidualWeld
    {kernel : Casimir.CasimirScalarModel}
    {F : Transverse.CasimirTransverseMeasureFamily kernel}
    (T : Tail.RegulatorTailEstimate)
    (R : RegulatorTailPointwiseRealisation {kernel} {F} T) : Set₁ where
  field
    residualAt : Nat → Spine.Carrier Residual.Real
    sequence : Spine.Sequence Residual.Real
    sequenceIsResidual : ∀ n →
      Spine._≈_ Residual.Real
        (Spine.sequenceAt Residual.Real sequence n)
        (residualAt n)

    ParameterWitness : Set
    parameterWitness : ParameterWitness
    candidate : Spine.Carrier Residual.Real

    sameMetricFamilyAsResidualTrajectory : Set
    sameMetricCandidateAsRenormalisedEnergy : Set

    metricTailImpliesBishopConvergence :
      Metric.PointwiseMetricConvergence (Tail.metricProblem T) →
      Spine.ConvergesTo Residual.Real sequence candidate

    reading : String

open RegulatorTailResidualWeld public

asDirectResidualMetricLimit :
  ∀ {kernel F}
    {T : Tail.RegulatorTailEstimate}
    {R : RegulatorTailPointwiseRealisation {kernel} {F} T} →
  RegulatorTailResidualWeld T R →
  Route.DirectResidualMetricLimit
asDirectResidualMetricLimit {T = T} {R = R} W = record
  { Route.residualAt = residualAt W
  ; Route.sequence = sequence W
  ; Route.sequenceIsResidual = sequenceIsResidual W
  ; Route.metricProblem = Tail.metricProblem T
  ; Route.metricConvergence = compilePointwiseMetricConvergence R
  ; Route.ParameterWitness = ParameterWitness W
  ; Route.parameterWitness = parameterWitness W
  ; Route.candidate = candidate W
  ; Route.sameLiteralResidualTrajectory = sameMetricFamilyAsResidualTrajectory W
  ; Route.sameCandidateLimit = sameMetricCandidateAsRenormalisedEnergy W
  ; Route.directMetricTailImpliesBishopConvergence = metricTailImpliesBishopConvergence W
  ; Route.reading = reading W
  }

compileRegulatorTailRoute :
  ∀ {kernel F}
    {T : Tail.RegulatorTailEstimate}
    {R : RegulatorTailPointwiseRealisation {kernel} {F} T} →
  RegulatorTailResidualWeld T R →
  Route.ResidualLimitResult
compileRegulatorTailRoute W =
  Route.compileResidualLimit
    (Route.viaDirectMetricTail (asDirectResidualMetricLimit W))

record ReverseRegulatorTailRouteObligations : Set where
  field
    existingRegulatorTailEstimateRealizedPointwise : Set
    sameResidualTrajectoryWeld : Set
    sameCandidateWeld : Set
    metricTailToBishopConvergenceTransport : Set

open ReverseRegulatorTailRouteObligations public

data DirectRegulatorTailStillRequiresSummableIncrementProof : Set where

noDuplicateIncrementPayment :
  DirectRegulatorTailStillRequiresSummableIncrementProof → ⊥
noDuplicateIncrementPayment ()

record Status : Set where
  field
    existingRegulatorTailCutsetReused : Bool
    directTailToResidualCompilerOwned : Bool
    independentIncrementProofRequired : Bool
    concreteTailEstimateClosed : Bool

    existingRegulatorTailCutsetReusedIsTrue : existingRegulatorTailCutsetReused ≡ true
    directTailToResidualCompilerOwnedIsTrue : directTailToResidualCompilerOwned ≡ true
    independentIncrementProofRequiredIsFalse : independentIncrementProofRequired ≡ false
    concreteTailEstimateClosedIsFalse : concreteTailEstimateClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { existingRegulatorTailCutsetReused = true
  ; directTailToResidualCompilerOwned = true
  ; independentIncrementProofRequired = false
  ; concreteTailEstimateClosed = false
  ; existingRegulatorTailCutsetReusedIsTrue = refl
  ; directTailToResidualCompilerOwnedIsTrue = refl
  ; independentIncrementProofRequiredIsFalse = refl
  ; concreteTailEstimateClosedIsFalse = refl
  }
