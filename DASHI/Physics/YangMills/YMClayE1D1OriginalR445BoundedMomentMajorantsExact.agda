module DASHI.Physics.YangMills.YMClayE1D1OriginalR445BoundedMomentMajorantsExact where

------------------------------------------------------------------------
-- Source-native M_eff,G and M_bare,F for the ORIGINAL R445 3 -> 1
-- quantitative Wilson covariance theorem.
--
-- If the selected real-valued original coarse tests have an explicit
-- pointwise nonnegative complement to unity, their pushforward/pure
-- original Wilson normalized moments are in [0,1].
--
-- The ACTUAL fine Gibbs state is the n=3 original Wilson measure;
-- the bare coarse state is the DIFFERENT n=1 original Wilson measure.
-- Neither law is replaced with an arbitrary probability oracle.
--
-- The source Haar/order/partition witnesses are the existing R445
-- originals. Real scalar division and abs positivity facts are kept
-- explicit. The physical moment RG discrepancy remains UNPAID.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Data.Product using (_×_; _,_)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _<ℝ_; _≤ℝ_; absℝ; oneNonnegative)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayE1A3OriginalR445CrossCutoffSourceExact as Cross
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteNumeratorOrderExact as Order
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact as Quant
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

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
    Cross.CoarseTest
      theory traceData exponential beta oneLink bilateral divide

  -- A coarse test and its explicitly supplied positive complement
  -- remain pointwise [0,1] when composed with the ACTUAL SU(N) block.
  originalEffectiveMomentAtMostOne :
    (test complement : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ test coarse) →
    (∀ coarse → 0ℝ ≤ℝ complement coarse) →
    (∀ coarse → test coarse +ℝ complement coarse ≡ 1ℝ) →
    0ℝ ≤ℝ
      Cross.originalR445EffectiveCoarseExpectation
        theory traceData exponential beta oneLink bilateral divide test
    ×
    (Cross.originalR445EffectiveCoarseExpectation
      theory traceData exponential beta oneLink bilateral divide test
      ≤ℝ 1ℝ)
  originalEffectiveMomentAtMostOne
    test complement testNN complementNN completes =
    let
      pullTest =
        Cross.originalFineBlockPullbackCylinder
          theory traceData exponential beta oneLink bilateral divide test 3
      pullComplement =
        Cross.originalFineBlockPullbackCylinder
          theory traceData exponential beta oneLink bilateral divide complement 3

      above =
        Order.originalWilsonNormalizedNonnegative
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak
          strict divideOrder divideZero
          3 pullTest
          (λ fine → testNN
            (Push.actualBlockedLinkMap
              theory traceData exponential (beta 3)
              oneLink bilateral divide fine))

      below =
        Order.originalWilsonNormalizedBelowOne
          theory traceData exponential beta oneLink bilateral divide
          ordered strictToWeak
          strict divideOrder divideSelf
          3 pullTest pullComplement
          (λ fine → complementNN
            (Push.actualBlockedLinkMap
              theory traceData exponential (beta 3)
              oneLink bilateral divide fine))
          (λ fine → completes
            (Push.actualBlockedLinkMap
              theory traceData exponential (beta 3)
              oneLink bilateral divide fine))
    in
    subst
      (λ v → 0ℝ ≤ℝ v × (v ≤ℝ 1ℝ))
      (Cross.originalE1FineBlockedIsR445EffectiveCoarse
        theory traceData exponential beta oneLink bilateral divide
        test)
      (above , below)

  originalBareMomentAtMostOne :
    (test complement : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ test coarse) →
    (∀ coarse → 0ℝ ≤ℝ complement coarse) →
    (∀ coarse → test coarse +ℝ complement coarse ≡ 1ℝ) →
    0ℝ ≤ℝ
      Cross.originalE1BareCoarseExpectation
        theory traceData exponential beta oneLink bilateral divide test
    ×
    (Cross.originalE1BareCoarseExpectation
      theory traceData exponential beta oneLink bilateral divide test
      ≤ℝ 1ℝ)
  originalBareMomentAtMostOne
    test complement testNN complementNN completes =
    (Order.originalWilsonNormalizedNonnegative
       theory traceData exponential beta oneLink bilateral divide
       ordered strictToWeak strict divideOrder divideZero
       1 test testNN)
    ,
    (Order.originalWilsonNormalizedBelowOne
       theory traceData exponential beta oneLink bilateral divide
       ordered strictToWeak strict divideOrder divideSelf
       1 test complement complementNN completes)

  originalEffectiveMomentAbsoluteAtMostOne :
    (test complement : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ test coarse) →
    (∀ coarse → 0ℝ ≤ℝ complement coarse) →
    (∀ coarse → test coarse +ℝ complement coarse ≡ 1ℝ) →
    absℝ
      (Cross.originalR445EffectiveCoarseExpectation
        theory traceData exponential beta oneLink bilateral divide test)
      ≤ℝ 1ℝ
  originalEffectiveMomentAbsoluteAtMostOne
    test complement testNN complementNN completes
    with originalEffectiveMomentAtMostOne
      test complement testNN complementNN completes
  ... | (nonnegative , upper) =
    subst (λ value → value ≤ℝ 1ℝ)
      (sym (absNonnegativeIsIdentity
        (Cross.originalR445EffectiveCoarseExpectation
          theory traceData exponential beta oneLink bilateral divide test)
        nonnegative))
      upper

  originalBareMomentAbsoluteAtMostOne :
    (test complement : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ test coarse) →
    (∀ coarse → 0ℝ ≤ℝ complement coarse) →
    (∀ coarse → test coarse +ℝ complement coarse ≡ 1ℝ) →
    absℝ
      (Cross.originalE1BareCoarseExpectation
        theory traceData exponential beta oneLink bilateral divide test)
      ≤ℝ 1ℝ
  originalBareMomentAbsoluteAtMostOne
    test complement testNN complementNN completes
    with originalBareMomentAtMostOne
      test complement testNN complementNN completes
  ... | (nonnegative , upper) =
    subst (λ value → value ≤ℝ 1ℝ)
      (sym (absNonnegativeIsIdentity
        (Cross.originalE1BareCoarseExpectation
          theory traceData exponential beta oneLink bilateral divide test)
        nonnegative))
      upper
