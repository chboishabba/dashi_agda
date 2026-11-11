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
open import Relation.Binary.PropositionalEquality using (sym; subst; trans; cong)
open import Data.Product using (_×_; _,_)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _-ℝ_; _<ℝ_; _≤ℝ_; absℝ; oneNonnegative; +-mono-≤; +-identityˡ; +-comm; +-assoc; *-distribˡ-+; mulOneʳ)

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
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445ThreeMomentRGCutExact as Source
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Hess

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

  ----------------------------------------------------------------------
  -- REAL bounded-test product closure on the SAME original coarse
  -- field. Given F + F^c = 1 and G + G^c = 1 with nonnegative parts,
  -- the product has the explicit nonnegative complement
  --
  --           (FG)^c = F^c + F * G^c.
  --
  -- This is a constructed physical-test-class closure, not a new
  -- event/measure axiom. In particular FG need not be a single loop.
  ----------------------------------------------------------------------

  sourceProductComplement :
    (left leftComplement right rightComplement : CoarseTest) →
    CoarseTest
  sourceProductComplement left leftComplement right rightComplement coarse =
    leftComplement coarse +ℝ
    (left coarse *ℝ rightComplement coarse)

  sourceProductTest :
    (left right : CoarseTest) → CoarseTest
  sourceProductTest left right coarse =
    left coarse *ℝ right coarse

  sourceProductNonnegative :
    (left right : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ left coarse) →
    (∀ coarse → 0ℝ ≤ℝ right coarse) →
    ∀ coarse →
      0ℝ ≤ℝ sourceProductTest left right coarse
  sourceProductNonnegative left right leftNN rightNN coarse =
    Hess.zeroProduct≤ (left coarse) (right coarse)
      (leftNN coarse) (rightNN coarse)

  sourceProductComplementNonnegative :
    (left leftComplement right rightComplement : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ left coarse) →
    (∀ coarse → 0ℝ ≤ℝ leftComplement coarse) →
    (∀ coarse → 0ℝ ≤ℝ rightComplement coarse) →
    ∀ coarse →
      0ℝ ≤ℝ
        sourceProductComplement
          left leftComplement right rightComplement coarse
  sourceProductComplementNonnegative
    left leftComplement right rightComplement
    leftNN leftCompNN rightCompNN coarse =
    subst
      (λ v → v ≤ℝ
        sourceProductComplement
          left leftComplement right rightComplement coarse)
      (+-identityˡ 0ℝ)
      (+-mono-≤
        (leftCompNN coarse)
        (Hess.zeroProduct≤
          (left coarse) (rightComplement coarse)
          (leftNN coarse) (rightCompNN coarse)))

  sourceProductCompletesOne :
    (left leftComplement right rightComplement : CoarseTest) →
    (∀ coarse → left coarse +ℝ leftComplement coarse ≡ 1ℝ) →
    (∀ coarse → right coarse +ℝ rightComplement coarse ≡ 1ℝ) →
    ∀ coarse →
      sourceProductTest left right coarse
      +ℝ sourceProductComplement
        left leftComplement right rightComplement coarse
      ≡ 1ℝ
  sourceProductCompletesOne
    left leftComplement right rightComplement
    leftComplete rightComplete coarse =
    let
      f = left coarse
      g = right coarse
      cf = leftComplement coarse
      cg = rightComplement coarse
    in
    trans
      (cong (λ v → (f *ℝ g) +ℝ v)
        (+-comm cf (f *ℝ cg)))
      (trans
        (sym (+-assoc (f *ℝ g) (f *ℝ cg) cf))
        (trans
          (cong (λ v → v +ℝ cf)
            (sym (*-distribˡ-+ f g cg)))
          (trans
            (cong (λ v → (f *ℝ v) +ℝ cf)
              (rightComplete coarse))
            (trans
              (cong (λ v → v +ℝ cf) (mulOneʳ f))
              (leftComplete coarse)))))

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

  ----------------------------------------------------------------------
  -- P0 bounded-test source application: replace BOTH unverified
  -- one-point majorants in the original quantitative R445 theorem by
  -- exact literal 1ℝ using native original Wilson product-Haar bounds.
  --
  -- Still unpaid: ε_{FG}, ε_F, ε_G original RG moment error bounds.
  ----------------------------------------------------------------------

  originalR445CovarianceBoundForNativeUnitBoundedTests :
    (left right leftComplement rightComplement : CoarseTest) →
    (∀ coarse → 0ℝ ≤ℝ left coarse) →
    (∀ coarse → 0ℝ ≤ℝ leftComplement coarse) →
    (∀ coarse → left coarse +ℝ leftComplement coarse ≡ 1ℝ) →
    (∀ coarse → 0ℝ ≤ℝ right coarse) →
    (∀ coarse → 0ℝ ≤ℝ rightComplement coarse) →
    (∀ coarse → right coarse +ℝ rightComplement coarse ≡ 1ℝ) →
    (errorProduct errorLeft errorRight : ℝ) →
    0ℝ ≤ℝ errorLeft →
    0ℝ ≤ℝ errorRight →
    absℝ
      (Quant.effectiveMoment
        theory traceData exponential beta oneLink bilateral divide
        (Quant.productTest
          theory traceData exponential beta oneLink bilateral divide
          left right)
       -ℝ
       Quant.bareMoment
         theory traceData exponential beta oneLink bilateral divide
         (Quant.productTest
           theory traceData exponential beta oneLink bilateral divide
           left right))
      ≤ℝ errorProduct →
    absℝ
      (Quant.effectiveMoment
        theory traceData exponential beta oneLink bilateral divide left
       -ℝ
       Quant.bareMoment
         theory traceData exponential beta oneLink bilateral divide left)
      ≤ℝ errorLeft →
    absℝ
      (Quant.effectiveMoment
        theory traceData exponential beta oneLink bilateral divide right
       -ℝ
       Quant.bareMoment
         theory traceData exponential beta oneLink bilateral divide right)
      ≤ℝ errorRight →
    absℝ
      (Source.sourceEffectiveCovariance
        theory traceData exponential beta oneLink bilateral divide
        left right
       -ℝ
       Source.sourceBareCovariance
        theory traceData exponential beta oneLink bilateral divide
        left right)
    ≤ℝ
      errorProduct +ℝ ((errorLeft *ℝ 1ℝ) +ℝ (1ℝ *ℝ errorRight))
  originalR445CovarianceBoundForNativeUnitBoundedTests
    left right leftComplement rightComplement
    leftNN leftComplementNN leftCompletes
    rightNN rightComplementNN rightCompletes
    errP errL errR errLNN errRNN productError leftError rightError =
    Quant.originalR445CovarianceErrorFromThreeSourceMoments
      theory traceData exponential beta oneLink bilateral divide
      left right errP errL errR 1ℝ 1ℝ
      errLNN oneNonnegative oneNonnegative errRNN
      productError leftError
      (originalEffectiveMomentAbsoluteAtMostOne
        right rightComplement rightNN rightComplementNN rightCompletes)
      (originalBareMomentAbsoluteAtMostOne
        left leftComplement leftNN leftComplementNN leftCompletes)
      rightError
