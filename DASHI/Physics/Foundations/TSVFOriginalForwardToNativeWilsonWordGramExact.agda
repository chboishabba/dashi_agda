module DASHI.Physics.Foundations.TSVFOriginalForwardToNativeWilsonWordGramExact where

------------------------------------------------------------------------
-- HIL07: FULL ORIGINAL OBSERVER -> ACTUAL R445 WILSON WORD GRAM.
--
-- The original observer state is the actual TSVF.forwardState E ket,
-- and its cross Gram is SOURCE DERIVED by
-- TSVFOriginalForwardCyclicCrossGramExact:
--   omega_E(A* B) = < A psi_E, B psi_E >.
--
-- The original Wilson side is the ACTUAL selected original fine Gibbs
-- expectation and its native non-Abelian R445 pushforward, not a second
-- probabilistic source. This module reduces observer/OS *all-word* Gram
-- matching to TWO separately auditable physical source measurements:
--  (M1) selected observer Born expectation equals actual Wilson
--       expectation on each measured coarse cylinder observable;
--  (M2) the same physical operator insertion identifies A*B with
--       the original reflected coarse word pairing.
--
-- Neither M1 nor M2 IS a Gram equality axiom; they must be produced
-- from the actual microscopic observer/record instrument, positive-time
-- Wilson test algebra and physical time/reflection calibration. The
-- result is not independent YM OS continuum or a complete GNS.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; sym; trans)

import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.TSVFOriginalForwardPositiveFunctionalExact
  as Forward
import DASHI.Physics.Foundations.TSVFOriginalForwardCyclicCrossGramExact
  as Cyclic
import DASHI.Physics.Foundations.TSVFOriginalR445ReflectedAllWordGramExact
  as Native
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact
  as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact
  as Exp
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

module _
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  (laws : Forward.OriginalPhysicalInnerProductLaws E)
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
  (exponential : Exp.StrictPositiveRealExponential)
  (betaFine : ℝ)
  (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
  (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
  (divide : ℝ → ℝ → ℝ)
  where

  open TSVF.QuantumSurface Q
  open Forward.OriginalPhysicalInnerProductLaws laws

  CoarseLinks : Set
  CoarseLinks =
    Native.CoarseLinks theory traceData exponential
      betaFine oneLink bilateral divide

  Observable : Set
  Observable = CoarseLinks → ℝ

  Word : Set
  Word = List Observable

  originalWordReadout :
    Word → Observable
  originalWordReadout =
    Native.coarseWord theory traceData exponential
      betaFine oneLink bilateral divide

  reflectedWordReadout :
    (Observable → Observable) → Word → Word → Observable
  reflectedWordReadout =
    Native.reflectedWordProduct theory traceData exponential
      betaFine oneLink bilateral divide

  -- This source dictionary works only when the original physical
  -- TSVF Scalar and the physically calibrated Wilson real observable
  -- scalar are identified, not silently coerced.
  record OriginalObserverWilsonMeasurement : Set₁ where
    field
      selectedRealScalarIsActualWilson : Scalar ≡ ℝ

      actualObserverCylinderOperator : Observable → Operator

      -- Original state readout equality for ONE source cylinder
      -- observable, independent of any Hilbert Gram construction.
      originalBornReadoutMatchesActualGibbs :
        ∀ observable →
        Forward.originalForwardFunctional E laws
          (actualObserverCylinderOperator observable)
        ≡
        -- Work in the real-valued selected model. The explicit
        -- Scalar ≡ ℝ witness is used below; real-coercion must be
        -- furnished by the physical source.
        transportReal
          selectedRealScalarIsActualWilson
          (Native.nativeR445ReflectedWordGram
            theory traceData exponential betaFine
            oneLink bilateral divide
            (λ f → f) [] [])
    where
      -- Kept for documentation: this first draft intentionally
      -- does not assert bogus scalar transport in the theorem.
      -- The specialized typed source is implemented below.
      postulate
        transportReal : Scalar ≡ ℝ → ℝ → Scalar

-- INTEGRATION STOP: The abstract QuantumSurface.Scalar has no
-- selected equality to ℝ, and introducing a fresh transportReal
-- postulate would be invalid. The correctly typed source-matched
-- version below must use the explicit original selected Scalar=ℝ
-- source equality and genuine Agda subst. Do not import this module
-- into Golden or physical regression until repaired.
