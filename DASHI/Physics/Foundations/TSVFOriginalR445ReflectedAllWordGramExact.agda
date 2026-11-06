module DASHI.Physics.Foundations.TSVFOriginalR445ReflectedAllWordGramExact where

------------------------------------------------------------------------
-- HIL07 / S10: SAME ORIGINAL WILSON MEASURE, ALL CYCLIC WORD GRAMS.
--
-- Specializes the original R445 source's all-observable pushforward to
-- a reflected pairing of arbitrary finite ordered coarse Wilson words.
-- No independent coarse measure, no new source J, no arbitrary Gram
-- oracle and no false inference from second-order covariance.
--
-- The selected *coarse* reflection is explicitly a supplied map on
-- physical observables, not a theorem that it intertwines the native
-- fine spatial reflection. Fine Wilson RP, half-space support,
-- source-exact TSVF observer identification and continuum OS remain
-- independent physical producer theorems.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _*ℝ_; 0ℝ; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNR445BlockedPushforwardR320CovarianceExact as R445
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  CoarseLinks : Set
  CoarseLinks = R445.CoarseLinks theory traceData exponential
    betaFine oneLink bilateral divide

  CoarseObservable : Set
  CoarseObservable = CoarseLinks → ℝ

  coarseWord : List CoarseObservable → CoarseObservable
  coarseWord [] coarse = 1ℝ
  coarseWord (letter ∷ rest) coarse =
    letter coarse *ℝ coarseWord rest coarse

  reflectedWordProduct :
    (reflectCoarse : CoarseObservable → CoarseObservable) →
    List CoarseObservable → List CoarseObservable → CoarseObservable
  reflectedWordProduct reflectCoarse left right coarse =
    reflectCoarse (coarseWord left) coarse *ℝ coarseWord right coarse

  originalFineReflectedWordGram :
    (reflectCoarse : CoarseObservable → CoarseObservable) →
    List CoarseObservable → List CoarseObservable → ℝ
  originalFineReflectedWordGram reflectCoarse left right =
    R445.originalBlockedFineExpectation
      theory traceData exponential betaFine oneLink bilateral divide
      (reflectedWordProduct reflectCoarse left right)

  nativeR445ReflectedWordGram :
    (reflectCoarse : CoarseObservable → CoarseObservable) →
    List CoarseObservable → List CoarseObservable → ℝ
  nativeR445ReflectedWordGram reflectCoarse left right =
    R445.actualPushedCoarseExpectation
      theory traceData exponential betaFine oneLink bilateral divide
      (reflectedWordProduct reflectCoarse left right)

  -- All left and right words, with any length and any selected coarse
  -- reflection operator: exact SAME original physical Wilson measure
  -- and its native pushforward, not a covariance-based extrapolation.
  actualNativeR445AllReflectedWordGrams :
    (reflectCoarse : CoarseObservable → CoarseObservable)
    (left right : List CoarseObservable) →
    originalFineReflectedWordGram reflectCoarse left right
      ≡ nativeR445ReflectedWordGram reflectCoarse left right
  actualNativeR445AllReflectedWordGrams reflectCoarse left right =
    R445.originalBlockedFineExpectationIsPushforward
      theory traceData exponential betaFine oneLink bilateral divide
      (reflectedWordProduct reflectCoarse left right)

  -- Actual OS positivity can be transported once it is independently
  -- proved on the correct physically reflected original Wilson tests.
  -- Positive Gibbs density alone is insufficient (child no-go).
  originalFineOSPositiveTransfersToNativeR445 :
    (reflectCoarse : CoarseObservable → CoarseObservable)
    (word : List CoarseObservable) →
    0ℝ ≤ℝ originalFineReflectedWordGram reflectCoarse word word →
    0ℝ ≤ℝ nativeR445ReflectedWordGram reflectCoarse word word
  originalFineOSPositiveTransfersToNativeR445
      reflectCoarse word finePositive =
    substNonnegative
      (actualNativeR445AllReflectedWordGrams reflectCoarse word word)
      finePositive
    where
      open import Relation.Binary.PropositionalEquality using (subst)

      substNonnegative : ∀ {x y : ℝ} →
        x ≡ y → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y
      substNonnegative equality positive =
        subst (λ value → 0ℝ ≤ℝ value) equality positive

-- NOTE: this finite real classical reflected pairing is NOT the
-- independently constructed complex OS Hilbert Gram and does not
-- establish original TSVF observer equivalence, positivity or Stone.
