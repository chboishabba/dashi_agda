module DASHI.Physics.YangMills.YMClayE1D1OriginalWilsonWordConcatenationR445Exact where

------------------------------------------------------------------------
-- Actual original SU(N) plaquette word concatenation -> multiplication.
--
-- This is a nontrivial exact bridge for P0 E1/D1: the third physical
-- RG test FG required by the quantitative covariance theorem is
-- again an ORIGINAL Wilson plaquette word: left ++ right.
--
-- It follows by induction on the original source word compiler,
-- then uses actual original fine/bare Haar numerator congruence to
-- transport the same result to X(FG), not to a synthetic functional.
--
-- No unproved physical RG rate or expectation multiplicativity
-- is asserted: E(FG) is NOT E(F)E(G).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _*ℝ_; _<ℝ_; _≤ℝ_;
   *-comm; *-assoc; mulOneʳ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as Wilson
import DASHI.Physics.YangMills.YMClayE1D1OriginalVariablePlaquetteWordsExact as Words
import DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringExact as Center

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  Word : Nat → Set
  Word = Words.PlaquetteWord
    theory traceData exponential beta oneLink bilateral divide

  wordValue :
    (n : Nat) → Word n →
    Variable.SUNPeriodicLinks theory n → ℝ
  wordValue =
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide

  -- All original changing cutoffs, not only the fixed 4->2 cut.
  originalWilsonWordAppendIsProduct :
    (n : Nat) (left right : Word n)
    (links : Variable.SUNPeriodicLinks theory n) →
    wordValue n (left ++ right) links
    ≡ (wordValue n left links *ℝ wordValue n right links)
  originalWilsonWordAppendIsProduct n [] right links =
    sym (trans
      (*-comm 1ℝ (wordValue n right links))
      (mulOneʳ (wordValue n right links)))
  originalWilsonWordAppendIsProduct n (p ∷ ps) right links =
    trans
      (cong
        (λ next →
          Wilson.originalLocalPlaquetteTraceAt
            theory traceData exponential beta oneLink bilateral divide
            n p links *ℝ next)
        (originalWilsonWordAppendIsProduct n ps right links))
      (sym (*-assoc
        (Wilson.originalLocalPlaquetteTraceAt
          theory traceData exponential beta oneLink bilateral divide n p links)
        (wordValue n ps links)
        (wordValue n right links)))

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
  where

  CoarseWord : Set
  CoarseWord = Words.PlaquetteWord
    theory traceData exponential beta oneLink bilateral divide 1

  coarseWordTest : CoarseWord →
    Center.CoarseTest
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak
  coarseWordTest =
    Words.originalWordObservable
      theory traceData exponential beta oneLink bilateral divide 1

  -- The actual original R445 cross numerator of a two-source
  -- pointwise product equals its X at the genuine concatenated word.
  -- This is independent of the unproved physical RG moment rate.
  originalR445WordProductCrossNumeratorIsConcatenation :
    (left right : CoarseWord) →
    Center.X theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak
      (λ coarse →
        coarseWordTest left coarse *ℝ coarseWordTest right coarse)
    ≡
    Center.X theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak (coarseWordTest (left ++ right))
  originalR445WordProductCrossNumeratorIsConcatenation left right =
    Center.crossNumeratorCongruent
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak
      (λ coarse →
        coarseWordTest left coarse *ℝ coarseWordTest right coarse)
      (coarseWordTest (left ++ right))
      (λ coarse →
        sym
          (originalWilsonWordAppendIsProduct
            theory traceData exponential beta oneLink bilateral divide
            1 left right coarse))
