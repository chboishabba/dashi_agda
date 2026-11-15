module DASHI.Physics.YangMills.YMClayOriginalPlaquetteTraceCyclicityInsufficientExact where

------------------------------------------------------------------------
-- P0.06 NEGATIVE CONTROL, not a candidate physical trace norm proof.
--
-- SUNMatrixRealTrace currently asks only for a trace function and its
-- cyclicity. For every real scalar k the constant function on the
-- selected certified SU(N) matrix carrier is cyclic. Its matrix-Wilson
-- value is exactly k on every group element.
--
-- Thus a claim of |Tr_norm U| <= 1 for ALL admissible trace records
-- would require |k| <= 1 for EVERY real k (for any inhabited SUN).
-- The actual finite complex matrix trace and its normalization/range
-- must be supplied independently. This negative control makes the
-- P0.06 mathematical missing source explicit, without inventing a
-- contradiction in the postulated real order.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _≤ℝ_; absℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace

constantCyclicRealTrace :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
    ℝ → Trace.SUNMatrixRealTrace {Scalar = ℝ} theory
constantCyclicRealTrace theory scalar = record
  { Trace.SUNMatrixRealTrace.normalizedRealTrace = λ _ → scalar
  ; Trace.SUNMatrixRealTrace.traceCyclic = λ A B → refl
  }

constantCyclicWilsonValue :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (scalar : ℝ) (U : SUN.SUNMatrixElement theory) →
    Trace.matrixWilsonValue
      (constantCyclicRealTrace theory scalar) U ≡ scalar
constantCyclicWilsonValue theory scalar U = refl

universalCyclicTraceBoundForcesAllScalarsBounded :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
    (∀ (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
       (U : SUN.SUNMatrixElement theory) →
       absℝ (Trace.matrixWilsonValue traceData U) ≤ℝ 1ℝ) →
    (scalar : ℝ) (U : SUN.SUNMatrixElement theory) →
    absℝ scalar ≤ℝ 1ℝ
universalCyclicTraceBoundForcesAllScalarsBounded
  theory bound scalar U =
  bound (constantCyclicRealTrace theory scalar) U

-- This does not assert an inhabited k outside [-1,1] in the abstract
-- postulated real carrier. It exhibits the exact strength demanded
-- by any purported proof from cyclicity alone.
