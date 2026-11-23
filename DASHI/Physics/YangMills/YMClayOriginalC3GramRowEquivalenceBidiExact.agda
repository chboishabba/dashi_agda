module DASHI.Physics.YangMills.YMClayOriginalC3GramRowEquivalenceBidiExact where

------------------------------------------------------------------------
-- SOURCE-FIRST ORIGINAL WILSON C3 FULL-GRAM-ROW EQUIVALENCE.
--
-- This module consumes EXACTLY the already original weighted Wilson
-- reflected real-Gram source. It DOES NOT create a new Wilson measure,
-- positive OS form, Hilbert space, Hamiltonian, or reflection.
--
-- Distinction: a zero diagonal <F,F>=0 does not imply a zero Gram row
-- in an arbitrary real bilinear form. The full row equivalence below
-- is an elementary type-safe observable/quotient guardrail; only genuine
-- OS positivity/Cauchy-Schwarz may identify its radical with OS null.
--
-- A source-conditional C3 action preserves full row equivalence, for
-- ALL original tests (not just invariant or pre-rotated tests), by
-- original C3^3=id and the original weighted Gram invariance.
-- SOURCE-WRITTEN; Agda 2.9 kernel NOT RUN; no Clay gap claim.
-- Prior mathematics: Wilson, Haar, OS, Balaban; original DASHI owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_)

import Data.Vec.Base as Vec
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayOriginalWilsonC3WeightedHaarTransferExact as WilsonC3
import DASHI.Physics.YangMills.YMClayOriginalC3WeightedOSGramBidiExact as Source

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (divide : ℝ → ℝ → ℝ)
  where

  OriginalVec : Set
  OriginalVec = Vec.Vec (SUN.SUNMatrixElement theory) Single.Count

  OriginalObservable : Set
  OriginalObservable = OriginalVec → ℝ

  rotate : OriginalObservable → OriginalObservable
  rotate = Source.rotate theory traceData exponential betaFine oneLink divide

  gram :
      (OriginalVec → OriginalVec) →
      OriginalObservable → OriginalObservable → ℝ
  gram =
    Source.originalReflectedGramEntry
      theory traceData exponential betaFine oneLink divide

  originalOrderThree :
    ∀ test links →
      rotate (rotate (rotate test)) links ≡ test links
  originalOrderThree =
    Source.originalC3ObservableOrderThree
      theory traceData exponential betaFine oneLink divide

  -- Equality of ALL reflected Gram row observations, not equality
  -- of functions and not diagonal-zero alone.
  OriginalGramRowEquivalent :
    (OriginalVec → OriginalVec) →
    OriginalObservable → OriginalObservable → Set
  OriginalGramRowEquivalent reflect left right =
    ∀ test → gram reflect left test ≡ gram reflect right test

  originalGramRowRefl :
    ∀ reflect left → OriginalGramRowEquivalent reflect left left
  originalGramRowRefl reflect left test = refl

  originalGramRowSym :
    ∀ reflect left right →
    OriginalGramRowEquivalent reflect left right →
    OriginalGramRowEquivalent reflect right left
  originalGramRowSym reflect left right same test = sym (same test)

  originalGramRowTrans :
    ∀ reflect left middle right →
    OriginalGramRowEquivalent reflect left middle →
    OriginalGramRowEquivalent reflect middle right →
    OriginalGramRowEquivalent reflect left right
  originalGramRowTrans reflect left middle right lm mr test =
    trans (lm test) (mr test)

  -- A congruence in the ORIGINAL real integrand on the right input.
  -- Required to replace rotate^3(test) by test without invoking
  -- function extensionality or silently identifying two carriers.
  originalGramRightPointwise :
    ∀ reflect left right other →
    (∀ links → right links ≡ other links) →
    gram reflect left right ≡ gram reflect left other
  originalGramRightPointwise reflect left right other same =
    Source.originalExpectationPointwiseCongruence
      theory traceData exponential betaFine oneLink divide
      (λ links → left (reflect links) *ℝ right links)
      (λ links → left (reflect links) *ℝ other links)
      (λ links →
        cong (λ value → left (reflect links) *ℝ value)
             (same links))

  -- Original C3 on BOTH coordinates of the same reflected Gram.
  sourceGramC3 :
    ∀ reflect →
    Source.ReflectionCommutesWithOriginalSpatialC3
      theory traceData exponential betaFine oneLink divide reflect →
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ left right →
    gram reflect (rotate left) (rotate right)
      ≡ gram reflect left right
  sourceGramC3 reflect commute canonical density left right =
    Source.originalReflectedGramC3Invariant
      theory traceData exponential betaFine oneLink divide
      reflect commute canonical density left right

  -- The genuinely useful quotient guardrail: if original F and G have
  -- identical full Gram rows, the ORIGINAL spatial rotation of both
  -- also has identical rows against EVERY unchanged original test.
  -- The threefold source action supplies the inverse test transport.
  originalC3PreservesAllGramRows :
    ∀ reflect →
    Source.ReflectionCommutesWithOriginalSpatialC3
      theory traceData exponential betaFine oneLink divide reflect →
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ left right →
    OriginalGramRowEquivalent reflect left right →
    OriginalGramRowEquivalent reflect (rotate left) (rotate right)
  originalC3PreservesAllGramRows
      reflect commute canonical density left right same test =
    trans
      (originalGramRightPointwise
        reflect (rotate left) test (rotate (rotate (rotate test)))
        (λ links → sym (originalOrderThree test links)))
      (trans
        (sourceGramC3 reflect commute canonical density
          left (rotate (rotate test)))
        (trans
          (same (rotate (rotate test)))
          (trans
            (sym (sourceGramC3 reflect commute canonical density
              right (rotate (rotate test))))
            (originalGramRightPointwise
              reflect (rotate right)
              (rotate (rotate (rotate test))) test
              (originalOrderThree test)))))

  -- Full-zero Gram row is stronger than a bare zero diagonal before
  -- positivity; C3 preserves this observational zero, again on ALL
  -- test vectors rather than only a chosen character projector.
  OriginalGramRowZero :
    (OriginalVec → OriginalVec) →
    OriginalObservable → Set
  OriginalGramRowZero reflect observable =
    ∀ test → gram reflect observable test ≡ 0ℝ

  originalC3PreservesAllGramRowZeros :
    ∀ reflect →
    Source.ReflectionCommutesWithOriginalSpatialC3
      theory traceData exponential betaFine oneLink divide reflect →
    Sort.constructedNativeC3CanonicalLabelGoal →
    WilsonC3.ActualOriginalC3GibbsActionInvariant
      theory traceData exponential betaFine oneLink divide →
    ∀ observable →
    OriginalGramRowZero reflect observable →
    OriginalGramRowZero reflect (rotate observable)
  originalC3PreservesAllGramRowZeros
      reflect commute canonical density observable zeroRow test =
    trans
      (originalGramRightPointwise
        reflect (rotate observable)
        test (rotate (rotate (rotate test)))
        (λ links → sym (originalOrderThree test links)))
      (trans
        (sourceGramC3 reflect commute canonical density
          observable (rotate (rotate test)))
        (zeroRow (rotate (rotate test))))

------------------------------------------------------------------------
-- Does NOT construct the physical quotient or same-H map. FULL
-- positive-time COMPLEX Wilson Gram/RP, genuine C3 action invariance
-- of CMP119 E/R/B/V, E1 convergence and T(t) commutation remain OPEN.
------------------------------------------------------------------------
