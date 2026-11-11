module DASHI.Physics.YangMills.YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact where

------------------------------------------------------------------------
-- Quantitative E1/D1 original Wilson 3 -> 1 RG covariance cut.
--
-- The R445 effective coarse Wilson source and the distinct original
-- bare side-two Wilson source have DIFFERENT expectations in general.
-- Three bounded moment errors, rather than assumed exact agreement,
-- control the difference between their connected covariances.
--
-- Reuse the repository's CMP116 original real product telescope
-- (BalabanDecoupledActivityHessian.productHeadTelescope).
-- The finite mixed-log J11 of the *original* Wilson fine Gibbs theory
-- equals the actual R445 effective covariance already, without inputs.
-- No new physical probability law, J oracle, RG density or OS H appears.
--
-- All numerical error and majorant hypotheses below are explicitly
-- physical source leaves; this module does not prove their estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality using (trans; sym)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; _+ℝ_; _-ℝ_; _*ℝ_; absℝ; _≤ℝ_;
         ≤ℝ-trans; +-mono-≤; absSubadditive; absAddSubadditive;
         absMul; mulMonotoneNonnegative)

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Hess
import DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact as Product
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445ThreeMomentRGCutExact as Source
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact as Same
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

-- Reusable exact 2-factor error telescope, with no YM hypotheses.
twoFactorDifferenceMajorant :
  (a b p q errorAB errorPQ boundP boundB : ℝ) →
  0ℝ ≤ℝ errorAB →
  0ℝ ≤ℝ boundP →
  0ℝ ≤ℝ boundB →
  0ℝ ≤ℝ errorPQ →
  absℝ (a -ℝ b) ≤ℝ errorAB →
  absℝ p ≤ℝ boundP →
  absℝ b ≤ℝ boundB →
  absℝ (p -ℝ q) ≤ℝ errorPQ →
  absℝ ((a *ℝ p) -ℝ (b *ℝ q))
    ≤ℝ (errorAB *ℝ boundP) +ℝ (boundB *ℝ errorPQ)
twoFactorDifferenceMajorant
  a b p q errorAB errorPQ boundP boundB
  errorABNN boundPNN boundBNN errorPQNN
  leftError rightSize leftSize rightError
  rewrite Hess.productHeadTelescope a b p q =
  ≤ℝ-trans
    (absAddSubadditive
      ((a -ℝ b) *ℝ p)
      (b *ℝ (p -ℝ q)))
    (+-mono-≤
      (transAbsMulLeft (a -ℝ b) p errorAB boundP
        leftError rightSize)
      (transAbsMulLeft b (p -ℝ q) boundB errorPQ
        leftSize rightError))
  where
  transAbsMulLeft :
    (left right boundLeft boundRight : ℝ) →
    absℝ left ≤ℝ boundLeft →
    absℝ right ≤ℝ boundRight →
    absℝ (left *ℝ right) ≤ℝ boundLeft *ℝ boundRight
  transAbsMulLeft left right boundLeft boundRight
    leftBound rightBound
    rewrite absMul left right =
    mulMonotoneNonnegative
      (Product.absNonnegative left) leftBound
      (Product.absNonnegative right) rightBound

-- Source-free algebraic covariance stability lemma. Crucially this
-- requires a majorant for the ACTUAL effective right moment and
-- the ACTUAL bare left moment, not a fictional uniform bound.
threeMomentCovarianceErrorBound :
  (effectiveProduct bareProduct
   effectiveLeft bareLeft effectiveRight bareRight
   errorProduct errorLeft errorRight
   boundEffectiveRight boundBareLeft : ℝ) →
  0ℝ ≤ℝ errorLeft →
  0ℝ ≤ℝ boundEffectiveRight →
  0ℝ ≤ℝ boundBareLeft →
  0ℝ ≤ℝ errorRight →
  absℝ (effectiveProduct -ℝ bareProduct) ≤ℝ errorProduct →
  absℝ (effectiveLeft -ℝ bareLeft) ≤ℝ errorLeft →
  absℝ effectiveRight ≤ℝ boundEffectiveRight →
  absℝ bareLeft ≤ℝ boundBareLeft →
  absℝ (effectiveRight -ℝ bareRight) ≤ℝ errorRight →
  absℝ
    ((effectiveProduct -ℝ (effectiveLeft *ℝ effectiveRight))
     -ℝ
     (bareProduct -ℝ (bareLeft *ℝ bareRight)))
    ≤ℝ
      errorProduct +ℝ
        ((errorLeft *ℝ boundEffectiveRight)
          +ℝ (boundBareLeft *ℝ errorRight))
threeMomentCovarianceErrorBound
  eP bP eL bL eR bR errP errL errR maxER maxBL
  errLNN maxERNN maxBLNN errRNN
  productError leftError rightSize leftSize rightError
  rewrite
    Hess.productHeadTelescope eL bL eR bR =
  ≤ℝ-trans
    (absSubadditive
      (eP -ℝ bP)
      ((eL -ℝ bL) *ℝ eR
       +ℝ bL *ℝ (eR -ℝ bR)))
    (+-mono-≤ productError
      (≤ℝ-trans
        (absAddSubadditive
          ((eL -ℝ bL) *ℝ eR)
          (bL *ℝ (eR -ℝ bR)))
        (+-mono-≤
          (productAbsBound (eL -ℝ bL) eR errL maxER
            leftError rightSize)
          (productAbsBound bL (eR -ℝ bR) maxBL errR
            leftSize rightError))))
  where
  productAbsBound :
    (x y mx my : ℝ) →
    absℝ x ≤ℝ mx →
    absℝ y ≤ℝ my →
    absℝ (x *ℝ y) ≤ℝ mx *ℝ my
  productAbsBound x y mx my xBound yBound
    rewrite absMul x y =
    mulMonotoneNonnegative
      (Product.absNonnegative x) xBound
      (Product.absNonnegative y) yBound

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

  CoarseTest : Set
  CoarseTest =
    Source.CoarseTest
      theory traceData exponential beta oneLink bilateral divide

  effectiveMoment : CoarseTest → ℝ
  effectiveMoment =
    Source.sourceEffectiveExpectation
      theory traceData exponential beta oneLink bilateral divide

  bareMoment : CoarseTest → ℝ
  bareMoment =
    Source.sourceBareExpectation
      theory traceData exponential beta oneLink bilateral divide

  productTest : CoarseTest → CoarseTest → CoarseTest
  productTest =
    Source.sourceCoarseProduct
      theory traceData exponential beta oneLink bilateral divide

  originalR445CovarianceQuantitativeThreeMomentBound :
    (left right : CoarseTest)
    (errorProduct errorLeft errorRight
     boundEffectiveRight boundBareLeft : ℝ) →
    0ℝ ≤ℝ errorLeft →
    0ℝ ≤ℝ boundEffectiveRight →
    0ℝ ≤ℝ boundBareLeft →
    0ℝ ≤ℝ errorRight →
    absℝ
      (effectiveMoment (productTest left right)
       -ℝ bareMoment (productTest left right))
      ≤ℝ errorProduct →
    absℝ (effectiveMoment left -ℝ bareMoment left)
      ≤ℝ errorLeft →
    absℝ (effectiveMoment right)
      ≤ℝ boundEffectiveRight →
    absℝ (bareMoment left)
      ≤ℝ boundBareLeft →
    absℝ (effectiveMoment right -ℝ bareMoment right)
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
      errorProduct +ℝ
        ((errorLeft *ℝ boundEffectiveRight)
          +ℝ (boundBareLeft *ℝ errorRight))
  originalR445CovarianceQuantitativeThreeMomentBound
    left right errP errL errR maxER maxBL
    errLNN maxERNN maxBLNN errRNN
    productError leftError rightSize leftSize rightError =
    threeMomentCovarianceErrorBound
      (effectiveMoment (productTest left right))
      (bareMoment (productTest left right))
      (effectiveMoment left)
      (bareMoment left)
      (effectiveMoment right)
      (bareMoment right)
      errP errL errR maxER maxBL
      errLNN maxERNN maxBLNN errRNN
      productError leftError rightSize leftSize rightError

  -- The original fine Wilson J11 coefficient is definitionally the
  -- same R445 effective covariance by the previous SOURCE proof.
  -- No physical CMP116 analyticity or continuum spectral gap follows.
  originalFineWilsonJ11QuantitativeRGMismatchBound :
    (left right : CoarseTest)
    (errorProduct errorLeft errorRight
     boundEffectiveRight boundBareLeft : ℝ) →
    0ℝ ≤ℝ errorLeft →
    0ℝ ≤ℝ boundEffectiveRight →
    0ℝ ≤ℝ boundBareLeft →
    0ℝ ≤ℝ errorRight →
    absℝ
      (effectiveMoment (productTest left right)
       -ℝ bareMoment (productTest left right))
      ≤ℝ errorProduct →
    absℝ (effectiveMoment left -ℝ bareMoment left)
      ≤ℝ errorLeft →
    absℝ (effectiveMoment right)
      ≤ℝ boundEffectiveRight →
    absℝ (bareMoment left)
      ≤ℝ boundBareLeft →
    absℝ (effectiveMoment right -ℝ bareMoment right)
      ≤ℝ errorRight →
    let directions =
          Original.originalWilsonLiteralJetDirections
            theory traceData exponential beta oneLink bilateral divide 3
    in
    absℝ
      (Cumulant.literalMixedSecondLogDerivative directions
        (Cumulant.sourceDirectionOf directions
          (Same.coarsePullback
            theory traceData exponential beta oneLink bilateral divide
            left))
        (Cumulant.sourceDirectionOf directions
          (Same.coarsePullback
            theory traceData exponential beta oneLink bilateral divide
            right))
       -ℝ
       Source.sourceBareCovariance
         theory traceData exponential beta oneLink bilateral divide
         left right)
    ≤ℝ
      errorProduct +ℝ
        ((errorLeft *ℝ boundEffectiveRight)
          +ℝ (boundBareLeft *ℝ errorRight))
  originalFineWilsonJ11QuantitativeRGMismatchBound
    left right errP errL errR maxER maxBL
    errLNN maxERNN maxBLNN errRNN
    productError leftError rightSize leftSize rightError
    rewrite
      Source.sourceEffectiveCovarianceIsActualR445
        theory traceData exponential beta oneLink bilateral divide
        left right
    | sym
      (Same.originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance
        theory traceData exponential beta oneLink bilateral divide
        left right) =
    originalR445CovarianceQuantitativeThreeMomentBound
      left right errP errL errR maxER maxBL
      errLNN maxERNN maxBLNN errRNN
      productError leftError rightSize leftSize rightError
