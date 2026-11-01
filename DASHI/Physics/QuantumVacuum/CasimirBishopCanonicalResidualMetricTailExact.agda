module DASHI.Physics.QuantumVacuum.CasimirBishopCanonicalResidualMetricTailExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Nat as Nat
import Data.Nat.Properties as NatP

import Real as Bishop
import Sequence as BishopSequence

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Physics.QuantumVacuum.CasimirRegulatorMetricTailReceiptExact as Tail

------------------------------------------------------------------------
-- CANONICAL BISHOP METRIC PROBLEM FOR ONE RESIDUAL TRAJECTORY
--
-- Precision is indexed by m : Nat and interpreted as 1/(m+1).  Thus Close is
-- total: no reciprocal of zero is ever formed.  Bishop's native convergence
-- constructor quantifies over k = suc m, so the two notions line up
-- definitionally after pattern matching on the nonzero k.
------------------------------------------------------------------------

bishopResidualMetricProblem :
  (residualAt : Nat → Bishop.ℝ) →
  (candidate : Bishop.ℝ) →
  Metric.ParameterisedMetricLimitProblem
bishopResidualMetricProblem residualAt candidate = record
  { Metric.Parameter = ⊤
  ; Metric.Index = Nat
  ; Metric.Value = Bishop.ℝ
  ; Metric.Epsilon = Nat
  ; Metric._≼_ = Nat._≤_
  ; Metric.Positive = λ _ → ⊤
  ; Metric.Close = λ x y precision →
      Bishop._≤_
        (Bishop.∣ Bishop._-_ x y ∣)
        (Bishop._⋆ (+ 1 / suc precision))
  ; Metric.family = λ _ index → residualAt index
  ; Metric.candidate = λ _ → candidate
  ; Metric.reading =
      "Canonical Bishop residual metric: precision index m means absolute error <= 1/(m+1)."
  }

canonicalTailToBishopConvergence :
  ∀ {residualAt candidate} →
  (T : Tail.ProofBearingMetricTail
    (bishopResidualMetricProblem residualAt candidate)) →
  BishopSequence._ConvergesTo_ residualAt candidate
canonicalTailToBishopConvergence {residualAt} {candidate} T =
  BishopSequence.con* λ
    { (suc precision) →
      let
        thresholdIndex = Tail.threshold T tt precision
      in
      thresholdIndex , λ n nAboveSuccessorThreshold →
        Tail.tailClose T
          tt
          precision
          tt
          n
          (NatP.≤-trans
            (NatP.n≤1+n thresholdIndex)
            nAboveSuccessorThreshold)
    }

------------------------------------------------------------------------
-- Same theorem with the metric receipt projected explicitly.
------------------------------------------------------------------------

canonicalPointwiseMetricConvergence :
  ∀ {residualAt candidate} →
  Tail.ProofBearingMetricTail
    (bishopResidualMetricProblem residualAt candidate) →
  Metric.PointwiseMetricConvergence
    (bishopResidualMetricProblem residualAt candidate)
canonicalPointwiseMetricConvergence = Tail.asPointwiseMetricConvergence

record ReverseCanonicalResidualTailObligations : Set where
  field
    dependentOneOverSuccessorTailBound : Set
    thresholdConstruction : Set
    presentationIndependence : Set
    reading : String

open ReverseCanonicalResidualTailObligations public

data SeparateMetricToBishopTransportStillRequired : Set where

data SeparateMetricFamilyIdentificationStillRequired : Set where

metricTransportIsDefinitionalHere :
  SeparateMetricToBishopTransportStillRequired → ⊥
metricTransportIsDefinitionalHere ()

metricFamilyIsLiteralResidualHere :
  SeparateMetricFamilyIdentificationStillRequired → ⊥
metricFamilyIsLiteralResidualHere ()

record Status : Set where
  field
    canonicalResidualMetricOwned : Bool
    totalSuccessorPrecisionOwned : Bool
    bishopNativeConvergenceCompilerOwned : Bool
    metricToBishopTransportLeafPruned : Bool
    metricFamilyIdentityLeafPruned : Bool
    concreteResidualTailBoundClosed : Bool

    canonicalResidualMetricOwnedIsTrue : canonicalResidualMetricOwned ≡ true
    totalSuccessorPrecisionOwnedIsTrue : totalSuccessorPrecisionOwned ≡ true
    bishopNativeConvergenceCompilerOwnedIsTrue : bishopNativeConvergenceCompilerOwned ≡ true
    metricToBishopTransportLeafPrunedIsTrue : metricToBishopTransportLeafPruned ≡ true
    metricFamilyIdentityLeafPrunedIsTrue : metricFamilyIdentityLeafPruned ≡ true
    concreteResidualTailBoundClosedIsFalse : concreteResidualTailBoundClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { canonicalResidualMetricOwned = true
  ; totalSuccessorPrecisionOwned = true
  ; bishopNativeConvergenceCompilerOwned = true
  ; metricToBishopTransportLeafPruned = true
  ; metricFamilyIdentityLeafPruned = true
  ; concreteResidualTailBoundClosed = false
  ; canonicalResidualMetricOwnedIsTrue = refl
  ; totalSuccessorPrecisionOwnedIsTrue = refl
  ; bishopNativeConvergenceCompilerOwnedIsTrue = refl
  ; metricToBishopTransportLeafPrunedIsTrue = refl
  ; metricFamilyIdentityLeafPrunedIsTrue = refl
  ; concreteResidualTailBoundClosedIsFalse = refl
  }
