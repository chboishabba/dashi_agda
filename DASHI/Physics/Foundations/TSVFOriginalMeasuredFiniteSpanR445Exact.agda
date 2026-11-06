module DASHI.Physics.Foundations.TSVFOriginalMeasuredFiniteSpanR445Exact where

------------------------------------------------------------------------
-- HIL07/HIL08: selected original TSVF observer -> actual native
-- Wilson R445 finite cyclic REAL span, on ONE physical measurement
-- source. No extra full-Gram premise.
--
-- Original physical M1/M2 are those already isolated in
-- TSVFOriginalForwardToNativeWilsonWordGramExact.  Using its theorem,
-- we instantiate the Golden finite span compiler and derive every
-- finite-real-combination Gram equality. No second physical
-- source readout, measure, reflection or Hilbert space is introduced.
--
-- The all-word real span is NOT a completed complex Hilbert:
-- sesquilinear and complex-conjugate coefficient laws, positivity,
-- continuity, dense image and Stone domain identification remain.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; _+ℝ_; _*ℝ_)

import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.TSVFOriginalForwardPositiveFunctionalExact as Forward
import DASHI.Physics.Foundations.TSVFOriginalForwardToNativeWilsonWordGramExact as Measurement
import DASHI.Physics.Foundations.TSVFOriginalCyclicFiniteSpanGramExact as FiniteSpan
import DASHI.Physics.Foundations.TSVFOriginalR445ReflectedAllWordGramExact as Native
import DASHI.Physics.Foundations.TSVFObserverOSCyclicGramSetoidExact as Gram
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

module _
    {Q : TSVF.QuantumSurface}
    (E : TSVF.TSVFEnsemble Q)
    (laws : Forward.OriginalPhysicalInnerProductLaws E)
    (observerRealReadout : TSVF.QuantumSurface.Scalar Q → ℝ)
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
    (source : Measurement.OriginalSameSourceMeasurement
      E laws observerRealReadout
      theory traceData exponential betaFine oneLink bilateral divide)
  where

  CoarseObservable : Set
  CoarseObservable =
    Native.CoarseLinks theory traceData exponential
      betaFine oneLink bilateral divide → ℝ

  Word : Set
  Word = List CoarseObservable

  selectedActualReflection : CoarseObservable → CoarseObservable
  selectedActualReflection =
    Measurement.OriginalSameSourceMeasurement.selectedPhysicalReflection
      source

  originalMeasuredWordPair : Word → Word → ℝ
  originalMeasuredWordPair =
    Measurement.originalMeasuredObserverCrossWordGram
      E laws observerRealReadout
      theory traceData exponential betaFine oneLink bilateral divide
      source

  originalNativeR445WordPair : Word → Word → ℝ
  originalNativeR445WordPair =
    Native.nativeR445ReflectedWordGram
      theory traceData exponential betaFine oneLink bilateral divide
      selectedActualReflection

  matchedActualWords : Gram.MatchedPhysicalCyclicWords Word Word ℝ
  matchedActualWords = record
    { observerPair = originalMeasuredWordPair
    ; osPair = originalNativeR445WordPair
    ; wordToOS = λ word → word
    ; allWordGramMatches =
        Measurement.originalMeasuredAllWordCrossGramEqualsNativeR445
          E laws observerRealReadout
          theory traceData exponential betaFine oneLink bilateral divide
          source
    }

  FiniteRealCyclicSpan : Set
  FiniteRealCyclicSpan = List (ℝ × Word)

  -- This is the compiled REAL Gram pairing on original forward
  -- observer cyclic cylinders; each pair is its SOURCE-MEASURED
  -- original TSVF expectation, not a new hypothetical OS state.
  measuredObserverSpanPair :
    FiniteRealCyclicSpan → FiniteRealCyclicSpan → ℝ
  measuredObserverSpanPair =
    FiniteSpan.finiteObserverGram
      0ℝ _+ℝ_ _*ℝ_ matchedActualWords

  mapActualSpan : FiniteRealCyclicSpan → FiniteRealCyclicSpan
  mapActualSpan =
    FiniteSpan.mapCyclicSpan
      0ℝ _+ℝ_ _*ℝ_ matchedActualWords

  literalNativeR445SpanPair :
    FiniteRealCyclicSpan → FiniteRealCyclicSpan → ℝ
  literalNativeR445SpanPair left right =
    FiniteSpan.finiteOSGram
      0ℝ _+ℝ_ _*ℝ_ matchedActualWords
      (mapActualSpan left) (mapActualSpan right)

  -- Full finite bilinear completion from the original M1/M2,
  -- for arbitrary pairs of real-weighted finite word combinations.
  originalMeasuredFiniteRealSpanEqualsActualNativeR445 :
    (left right : FiniteRealCyclicSpan) →
    measuredObserverSpanPair left right
      ≡ literalNativeR445SpanPair left right
  originalMeasuredFiniteRealSpanEqualsActualNativeR445 =
    FiniteSpan.originalAllFiniteSpanGramsMatch
      0ℝ _+ℝ_ _*ℝ_ matchedActualWords

  originalMeasuredFiniteSpanDiagonalEqualsNativeR445 :
    (span : FiniteRealCyclicSpan) →
    measuredObserverSpanPair span span
      ≡ literalNativeR445SpanPair span span
  originalMeasuredFiniteSpanDiagonalEqualsNativeR445 =
    FiniteSpan.originalAllFiniteSpanDiagonalMatches
      0ℝ _+ℝ_ _*ℝ_ matchedActualWords


  -- Two finite spans are experimentally Gram-indistinguishable iff
  -- they pair equally against every selected finite source test.
  -- This is a literal original-observer/R445 image setoid compiler,
  -- not the OS completed Hilbert null relation.
  OriginalFiniteSpanIndistinguishable :
    FiniteRealCyclicSpan → FiniteRealCyclicSpan → Set
  OriginalFiniteSpanIndistinguishable left right =
    (test : FiniteRealCyclicSpan) →
    measuredObserverSpanPair left test
      ≡ measuredObserverSpanPair right test

  NativeR445ImageSpanIndistinguishable :
    FiniteRealCyclicSpan → FiniteRealCyclicSpan → Set
  NativeR445ImageSpanIndistinguishable left right =
    (test : FiniteRealCyclicSpan) →
    literalNativeR445SpanPair left test
      ≡ literalNativeR445SpanPair right test

  originalFiniteSpanIndistinguishabilityBidi :
    (left right : FiniteRealCyclicSpan) →
    OriginalFiniteSpanIndistinguishable left right →
    NativeR445ImageSpanIndistinguishable left right
  originalFiniteSpanIndistinguishabilityBidi left right match test =
    trans
      (sym (originalMeasuredFiniteRealSpanEqualsActualNativeR445
        left test))
      (trans (match test)
        (originalMeasuredFiniteRealSpanEqualsActualNativeR445
          right test))

  nativeR445ImageIndistinguishabilityReflectsObserver :
    (left right : FiniteRealCyclicSpan) →
    NativeR445ImageSpanIndistinguishable left right →
    OriginalFiniteSpanIndistinguishable left right
  nativeR445ImageIndistinguishabilityReflectsObserver left right match test =
    trans
      (originalMeasuredFiniteRealSpanEqualsActualNativeR445
        left test)
      (trans (match test)
        (sym (originalMeasuredFiniteRealSpanEqualsActualNativeR445
          right test)))

-- The intended original physical completion must construct the
-- M1 same-instrument Born/Wilson cylinder equality and M2
-- star/reflection/product compatibility, rather than assuming them.
-- A true complex sesquilinear extension, original YM OS positivity,
-- Cauchy completion, cyclic density and Stone are still unpaid.
