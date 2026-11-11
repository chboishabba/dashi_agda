module DASHI.Physics.YangMills.YMClayE1D1OriginalSUNTraceToAllWordsBoundExact where

------------------------------------------------------------------------
-- P0.06: transfer a GENUINE matrix-SU(N) trace range to ALL original
-- physical varying-cutoff Wilson plaquettes and finite trace words.
--
-- No invented trace bound: the exactly missing concrete matrix proof
-- is a parameter on the ORIGINAL selected trace data. This module
-- proves that one theorem suffices for arbitrary source plaquette
-- locations, cutoffs and word lengths, using the actual signed
-- holonomy and original Wilson-word evaluator.
--
-- Specifically:
--   |Tr_norm(U)| <= 1 for all certified SUN matrix elements
--   => |F_{p,n}(links)| <= 1 for every original periodic plaquette
--   => |W_{word,n}(links)| <= 1 for every original trace word.
--
-- Unlike cyclicity (which admits arbitrary constant-valued traces),
-- the analytic SU(N) trace bound is NOT proved by this module.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans; subst)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _*ℝ_; _≤ℝ_; absℝ; absMul;
   oneNonnegative; mulOneʳ; mulMonotoneNonnegative; ≤ℝ-refl)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as Wilson
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
    (traceRange :
      ∀ (U : SUN.SUNMatrixElement theory) →
      absℝ (Trace.matrixWilsonValue traceData U) ≤ℝ 1ℝ)
    (absNonnegative :
      ∀ value → 0ℝ ≤ℝ absℝ value)
    (absOne : absℝ 1ℝ ≡ 1ℝ)
  where

  originalPlaquetteTraceBoundAtEveryCutoff :
    (n : Nat) (plaquette : Plaquette.PeriodicPlaquette n)
    (links : Variable.SUNPeriodicLinks theory n) →
    absℝ (Wilson.originalLocalPlaquetteTraceAt
      theory traceData exponential beta oneLink bilateral divide
      n plaquette links)
      ≤ℝ 1ℝ
  originalPlaquetteTraceBoundAtEveryCutoff n plaquette links =
    traceRange
      (Variable.periodicSUNPositivePlaquette theory n links plaquette)

  -- This is a definitional/source-algebra identity: a singleton
  -- Wilson word has the true matrix trace, not a formal independent
  -- "one-plaquette" test postulate.
  originalSingletonWordIsPlaquetteTrace :
    (n : Nat) (plaquette : Plaquette.PeriodicPlaquette n)
    (links : Variable.SUNPeriodicLinks theory n) →
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n (plaquette ∷ []) links
    ≡
    Wilson.originalLocalPlaquetteTraceAt
      theory traceData exponential beta oneLink bilateral divide
      n plaquette links
  originalSingletonWordIsPlaquetteTrace n plaquette links =
    mulOneʳ
      (Wilson.originalLocalPlaquetteTraceAt
        theory traceData exponential beta oneLink bilateral divide
        n plaquette links)

  originalAllLengthWilsonWordMagnitudeBound :
    (n : Nat) (word : Words.PlaquetteWord
      theory traceData exponential beta oneLink bilateral divide n)
    (links : Variable.SUNPeriodicLinks theory n) →
    absℝ (Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide
      n word links)
      ≤ℝ 1ℝ
  originalAllLengthWilsonWordMagnitudeBound n [] links =
    subst
      (λ value → value ≤ℝ 1ℝ)
      (sym absOne)
      (≤ℝ-refl {a = 1ℝ})
  originalAllLengthWilsonWordMagnitudeBound n (p ∷ ps) links =
    let
      x = Wilson.originalLocalPlaquetteTraceAt
        theory traceData exponential beta oneLink bilateral divide
        n p links
      y = Words.originalWordObservable
        theory traceData exponential beta oneLink bilateral divide
        n ps links
    in
    subst
      (λ value → value ≤ℝ 1ℝ)
      (sym (mulOneʳ 1ℝ))
      (subst
        (λ value → value ≤ℝ 1ℝ *ℝ 1ℝ)
        (sym (absMul x y))
        (mulMonotoneNonnegative
          (absNonnegative x)
          (originalPlaquetteTraceBoundAtEveryCutoff n p links)
          (absNonnegative y)
          (originalAllLengthWilsonWordMagnitudeBound n ps links)))
