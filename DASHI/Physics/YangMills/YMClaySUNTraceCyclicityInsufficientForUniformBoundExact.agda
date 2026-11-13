module DASHI.Physics.YangMills.YMClaySUNTraceCyclicityInsufficientForUniformBoundExact where

-- P0 trace authority audit: the ORIGINAL SUNMatrixRealTrace record
-- assumes CYCLICITY of a function Matrix → Scalar, but no normalization,
-- no finite-dimensional diagonal formula, and no entrywise Cauchy-Schwarz.
--
-- Thus cyclicity alone does not prove the original Wilson normalized
-- trace bound |Re Tr(U)/N| ≤ 1.  The following counterinstance is
-- defined for EVERY certified SU(N) matrix theory: a constant rational
-- "trace" equal to 2. It is exactly cyclic but takes 2 at identity,
-- contradicting the desired normalization 1. This is a typed API
-- obstruction, not a model of the physical normalized trace.
--
-- Full P0 trace needs an enhanced finite complex matrix/trace authority
-- proving Tr(I)=N and |Tr(U)|≤N from unitary entrywise/operator bounds,
-- then a same-object equality to the original RealAnalysisAxioms scalar.
--
-- Source no-go, NOT a physical SU(N) trace construction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _/_)
open import Relation.Binary.PropositionalEquality using (_≢_)
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace

constantTwoCyclicTrace :
  ∀ {Matrix Complex : Set} {N : Nat} →
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  Trace.SUNMatrixRealTrace {Scalar = ℚ} theory
constantTwoCyclicTrace theory = record
  { Trace.SUNMatrixRealTrace.normalizedRealTrace = λ _ → + 2 / 1
  ; Trace.SUNMatrixRealTrace.traceCyclic = λ A B → refl
  }

constantTraceAtEveryOriginalSUNElement :
  ∀ {Matrix Complex : Set} {N : Nat} →
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  (U : SUN.SUNMatrixElement theory) →
  Trace.matrixWilsonValue (constantTwoCyclicTrace theory) U
  ≡ (+ 2 / 1)
constantTraceAtEveryOriginalSUNElement theory U = refl

constantCyclicTraceNotNormalizedAtIdentity :
  ∀ {Matrix Complex : Set} {N : Nat} →
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  Trace.matrixWilsonValue
    (constantTwoCyclicTrace theory) (SUN.sunIdentity theory)
  ≢ 1ℚ
constantCyclicTraceNotNormalizedAtIdentity theory ()

-- As the goal is the precise original SU(N) physically-normalized
-- trace, this counterexample must be REJECTED at the trace-authority
-- boundary; not by introducing a new cyclicity or Haar axiom.
