module DASHI.Physics.YangMills.YMClayR445OneLocalTVThreeMomentsSourceWeldExact where

------------------------------------------------------------------------
-- R445 SAME ORIGINAL 1024-LINK WILSON / COARSE-PUSHFORWARD SOURCE.
--
-- Existing sources:
-- * E1A3OriginalR445CrossCutoffSourceExact : ORIGINAL beta(3)
--   fine Wilson Gibbs 3->1 effective normalized coarse expectation
--   against DIFFERENT original bare coarse beta(1) expectation;
-- * E1D1OriginalR445BoundedMomentMajorantsExact : physical normalized
--   F,G,FG and explicit complementary tests, two unit moment bounds;
-- * E1D1OriginalR445QuantitativeThreeMomentRGCutExact : quantitative
--   physical Wilson covariance discrepancy from three source moments.
--
-- NEW: a genuinely same-source CONSUMER reducing all three errors
-- to ONE uniform local observation-algebra TV discrepancy.  This is
-- a theorem on the original source expectation functions, not
-- about an invented finite mock probability space. In particular
-- it never equates the effective and bare Wilson laws.
--
-- INPUT STILL UNPAID:
--   for all original bounded coarse tests, the absolute difference
--   between ACTUAL normalized expectations <= localTV.
--   In measure theory this follows from an actual projectively
--   localized TV bound on the original restricted measure.
--   Full-volume TV need not vanish, even when observable-marginal
--   TV does. DO NOT assume the source physical input is true.
--
-- No new postulates and no physical continuum/E1/D1/D2 endpoint.
-- Still requires Agda 2.9/axiom closure verification; original scalar
-- RealAnalysisAxioms includes legacy postulates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; _≤ℝ_; _<ℝ_; absℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445ThreeMomentRGCutExact as Source
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact as Quant
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445BoundedMomentMajorantsExact as Bounded

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
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (divideOrder :
      ∀ {a b denominator : ℝ} →
      0ℝ <ℝ denominator →
      a ≤ℝ b →
      divide a denominator ≤ℝ divide b denominator)
    (divideSelf :
      ∀ denominator → 0ℝ <ℝ denominator →
      divide denominator denominator ≡ 1ℝ)
    (divideZero :
      ∀ denominator → 0ℝ <ℝ denominator →
      divide 0ℝ denominator ≡ 0ℝ)
    (absNonnegativeIsIdentity :
      ∀ value → 0ℝ ≤ℝ value → absℝ value ≡ value)
  where

  CoarseTest : Set
  CoarseTest =
    Quant.CoarseTest
      theory traceData exponential beta oneLink bilateral divide

  -- Exactly ONE physical local-TV target over the native original
  -- coarse observation algebra. The positivity/complement tests
  -- make the universally quantified family genuinely bounded [0,1].
  OriginalBoundedObservationLocalTV : ℝ → Set
  OriginalBoundedObservationLocalTV localTV =
    (test complement : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ test coarse) →
    (∀ coarse → 0ℝ ≤ℝ complement coarse) →
    (∀ coarse → test coarse +ℝ complement coarse ≡ 1ℝ) →
    absℝ
      (Quant.effectiveMoment
        theory traceData exponential beta oneLink bilateral divide test
       -ℝ
       Quant.bareMoment
        theory traceData exponential beta oneLink bilateral divide test)
      ≤ℝ localTV

  -- NO new epsilon_F, epsilon_G and epsilon_FG assumptions:
  -- All three follow by applying the SAME original local-TV
  -- statement to the selected three actual bounded coarse tests.
  originalPhysicalR445CovarianceFromOneLocalTV :
    (left right leftComplement rightComplement
      productComplement : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ left coarse) →
    (∀ coarse → 0ℝ ≤ℝ leftComplement coarse) →
    (∀ coarse → left coarse +ℝ leftComplement coarse ≡ 1ℝ) →
    (∀ coarse → 0ℝ ≤ℝ right coarse) →
    (∀ coarse → 0ℝ ≤ℝ rightComplement coarse) →
    (∀ coarse → right coarse +ℝ rightComplement coarse ≡ 1ℝ) →
    (∀ coarse → 0ℝ ≤ℝ
      Quant.productTest
        theory traceData exponential beta oneLink bilateral divide
        left right coarse) →
    (∀ coarse → 0ℝ ≤ℝ productComplement coarse) →
    (∀ coarse →
      Quant.productTest
        theory traceData exponential beta oneLink bilateral divide
        left right coarse
      +ℝ productComplement coarse ≡ 1ℝ) →
    (localTV : ℝ) → 0ℝ ≤ℝ localTV →
    OriginalBoundedObservationLocalTV localTV →
    absℝ
      (Source.sourceEffectiveCovariance
        theory traceData exponential beta oneLink bilateral divide
        left right
       -ℝ
       Source.sourceBareCovariance
        theory traceData exponential beta oneLink bilateral divide
        left right)
    ≤ℝ
      localTV +ℝ ((localTV *ℝ 1ℝ) +ℝ (1ℝ *ℝ localTV))
  originalPhysicalR445CovarianceFromOneLocalTV
    left right leftComp rightComp productComp
    leftNN leftCompNN leftComplete
    rightNN rightCompNN rightComplete
    prodNN prodCompNN prodComplete
    localTV localTVNN tv =
    Bounded.originalR445CovarianceBoundForNativeUnitBoundedTests
      theory traceData exponential beta oneLink bilateral divide
      ordered strictToWeak strict divideOrder divideSelf divideZero
      absNonnegativeIsIdentity
      left right leftComp rightComp
      leftNN leftCompNN leftComplete
      rightNN rightCompNN rightComplete
      localTV localTV localTV localTVNN localTVNN
      (tv
        (Quant.productTest
          theory traceData exponential beta oneLink bilateral divide
          left right)
        productComp
        prodNN prodCompNN prodComplete)
      (tv left leftComp leftNN leftCompNN leftComplete)
      (tv right rightComp rightNN rightCompNN rightComplete)
