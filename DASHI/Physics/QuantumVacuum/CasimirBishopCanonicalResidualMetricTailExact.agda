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
-- Use Nat epsilon indices directly:
--
--   Close x y k  := |x-y| <= 1/k,
--
-- with Positive k := NonZero k.  This matches Bishop Sequence.ConvergesTo
-- exactly enough that a proof-bearing metric tail compiles directly to the
-- native convergence constructor.  No separate metric-to-Bishop theorem is
-- required.
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
  ; Metric.Positive = Nat.NonZero
  ; Metric.Close = λ x y k →
      Bishop._≤_
        (Bishop.∣ Bishop._-_ x y ∣)
        (Bishop._⋆ (+ 1 / k))
  ; Metric.family = λ _ index → residualAt index
  ; Metric.candidate = λ _ → candidate
  ; Metric.reading =
      "Canonical Bishop residual metric: Nat epsilon index k means absolute error <= 1/k."
  }

canonicalTailToBishopConvergence :
  ∀ {residualAt candidate} →
  (T : Tail.ProofBearingMetricTail
    (bishopResidualMetricProblem residualAt candidate)) →
  BishopSequence._ConvergesTo_ residualAt candidate
canonicalTailToBishopConvergence {residualAt} {candidate} T =
  BishopSequence.con* λ k {{kNonzero}} →
    let
      thresholdIndex = Tail.threshold T tt k
    in
    thresholdIndex , λ n nAboveSuccessorThreshold →
      Tail.tailClose T
        tt
        k
        kNonzero
        n
        (NatP.≤-trans
          (NatP.n≤1+n thresholdIndex)
          nAboveSuccessorThreshold)

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
    dependentOneOverKTailBound : Set
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
    bishopNativeConvergenceCompilerOwned : Bool
    metricToBishopTransportLeafPruned : Bool
    metricFamilyIdentityLeafPruned : Bool
    concreteResidualTailBoundClosed : Bool

    canonicalResidualMetricOwnedIsTrue : canonicalResidualMetricOwned ≡ true
    bishopNativeConvergenceCompilerOwnedIsTrue : bishopNativeConvergenceCompilerOwned ≡ true
    metricToBishopTransportLeafPrunedIsTrue : metricToBishopTransportLeafPruned ≡ true
    metricFamilyIdentityLeafPrunedIsTrue : metricFamilyIdentityLeafPruned ≡ true
    concreteResidualTailBoundClosedIsFalse : concreteResidualTailBoundClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { canonicalResidualMetricOwned = true
  ; bishopNativeConvergenceCompilerOwned = true
  ; metricToBishopTransportLeafPruned = true
  ; metricFamilyIdentityLeafPruned = true
  ; concreteResidualTailBoundClosed = false
  ; canonicalResidualMetricOwnedIsTrue = refl
  ; bishopNativeConvergenceCompilerOwnedIsTrue = refl
  ; metricToBishopTransportLeafPrunedIsTrue = refl
  ; metricFamilyIdentityLeafPrunedIsTrue = refl
  ; concreteResidualTailBoundClosedIsFalse = refl
  }
