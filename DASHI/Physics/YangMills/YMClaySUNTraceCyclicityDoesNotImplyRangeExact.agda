module DASHI.Physics.YangMills.YMClaySUNTraceCyclicityDoesNotImplyRangeExact where

------------------------------------------------------------------------
-- ORIGINAL MATRIX-SU(N) TRACE AUTHORITY: EXACT INTERFACE COUNTERMODEL.
--
-- The actual record SUNMatrixRealTrace in the original Wilson source
-- requires only a Scalar-valued matrix function and trace CYCLICITY.
-- It does NOT require that this function equals Re(Tr(M))/N, or has
-- normalized trace range. This matters for P0.Trace and P0.F.
--
-- An arbitrary CONSTANT "trace" satisfies the selected cyclicity
-- axiom. In particular the Nat-valued constant two trace satisfies
-- ALL fields of SUNMatrixRealTrace on any given certified SUN matrix
-- theory, but at the ORIGINAL source-owned sunIdentity its value is
-- two, not in {zero,one}. Therefore even the toy natural-number
-- analogue of the claimed unit bound cannot follow parametrically
-- from the original trace interface.
--
-- This is NOT a counterexample to the TRUE analytic theorem that
-- normalized real traces of genuine unitary complex matrices have
-- absolute value <= 1. It isolates the missing mathematical SOURCE
-- implementation: actual indexed C-matrix entries, unitarity row
-- orthogonality, complex Cauchy-Schwarz, real part and normalized sum,
-- and equality with SUNMatrixRealTrace.normalizedRealTrace.
--
-- Does not define an independent Wilson measure, postulate a trace
-- inequality, or claim arbitrary SU(N) bounds. No new postulates.
-- SOURCE-WRITTEN ONLY: pinned Agda 2.9 kernel receipt is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace

-- Every constant is CYCLIC, regardless of whether it is the usual
-- normalized real matrix trace. The missing range condition cannot
-- be proved by cyclicity alone.
constantCyclicTrace :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (constant : Nat) →
  Trace.SUNMatrixRealTrace {Scalar = Nat} theory
constantCyclicTrace theory constant = record
  { Trace.SUNMatrixRealTrace.normalizedRealTrace = λ _ → constant
  ; Trace.SUNMatrixRealTrace.traceCyclic = λ _ _ → refl
  }

-- This uses EXACTLY the original source's matrixWilsonValue, not a
-- synthetic trace evaluator; its constant field reduces definitionally.
originalMatrixWilsonValueOfConstantTrace :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (constant : Nat)
    (U : SUN.SUNMatrixElement theory) →
  Trace.matrixWilsonValue (constantCyclicTrace theory constant) U
    ≡ constant
originalMatrixWilsonValueOfConstantTrace theory constant U = refl

-- A very weak native "unit interval" on Nat is enough for a genuine
-- semantic counterexample; no imported real order or abs axioms.
NatAtMostOne : Nat → Set
NatAtMostOne value = (value ≡ zero) ⊎ (value ≡ suc zero)

twoIsNotAtMostOne : NatAtMostOne (suc (suc zero)) → ⊥
twoIsNotAtMostOne (inj₁ ())
twoIsNotAtMostOne (inj₂ ())

-- The original constructor SUN.sunIdentity exists for EVERY certified
-- matrix theory. If one tried to derive a bounded-trace result for ALL
-- source SUNMatrixRealTrace records from mere cyclicity, the genuine
-- original identity configuration with the constant-two record
-- immediately refutes it.
originalSUNTraceCyclicityAloneCannotForceUnitRange :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  ((traceData : Trace.SUNMatrixRealTrace {Scalar = Nat} theory)
   (U : SUN.SUNMatrixElement theory) →
   NatAtMostOne (Trace.matrixWilsonValue traceData U)) →
  ⊥
originalSUNTraceCyclicityAloneCannotForceUnitRange
    theory allegedRange =
  twoIsNotAtMostOne
    (allegedRange
      (constantCyclicTrace theory (suc (suc zero)))
      (SUN.sunIdentity theory))

-- Physical P0.Trace is only paid upon constructing a SPECIFIC record
-- tied to the true indexed complex matrix trace and proving the usual
-- absolute-value range for that record. This countermodel only
-- invalidates the proposed generic traceCyclic -> traceRange weld.
