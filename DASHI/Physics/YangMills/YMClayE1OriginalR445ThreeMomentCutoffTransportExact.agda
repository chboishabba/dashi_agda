module DASHI.Physics.YangMills.YMClayE1OriginalR445ThreeMomentCutoffTransportExact where

------------------------------------------------------------------------
-- ACTUAL ORIGINAL E1 CUTOFF-3/1 -> R445 THREE-MOMENT RG WELD.
--
-- This source does NOT construct a new bare Wilson measure or a new
-- effective measure.  The fine side is the ORIGINAL n=3 periodic
-- Wilson expectation of the ACTUAL side-four -> side-two blocked
-- observable; the bare side is the ORIGINAL n=1 Wilson expectation.
--
-- Original owner E1A3 ALREADY proves the literal same-object equality
-- E1 finite original n=3 blocked = R445 original effective.
-- R445 ThreeMoment original owner ALREADY defines effective/bare F,G,
-- FG and their connected covariances on that SAME exact physical
-- Wilson source. The quantitative R445 owner ALREADY proves the
-- covariance telescope from three moment errors.
--
-- The new result is the missing THREE-TEST transport of the ACTUAL
-- E1 changing-cutoff error into that quantitative physical R445 input,
-- with no fake 1/k, geometric 4^-k or UV-uniform RG estimate.
--
-- Neither changing-cutoff E1 convergence nor physical D1/D2 follows.
-- SOURCE-WRITTEN; local pinned Agda 2.9 kernel receipt required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_; _-ℝ_; absℝ; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayE1A3OriginalR445CrossCutoffSourceExact as E1A3
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445ThreeMomentRGCutExact as R445
import DASHI.Physics.YangMills.YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact as Quant

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
    E1A3.CoarseTest
      theory traceData exponential beta oneLink bilateral divide

  originalE1FineBlocked : CoarseTest → ℝ
  originalE1FineBlocked =
    E1A3.originalE1FineBlockedExpectation
      theory traceData exponential beta oneLink bilateral divide

  originalE1BareCoarse : CoarseTest → ℝ
  originalE1BareCoarse =
    E1A3.originalE1BareCoarseExpectation
      theory traceData exponential beta oneLink bilateral divide

  originalR445Effective : CoarseTest → ℝ
  originalR445Effective =
    R445.sourceEffectiveExpectation
      theory traceData exponential beta oneLink bilateral divide

  originalR445Bare : CoarseTest → ℝ
  originalR445Bare =
    R445.sourceBareExpectation
      theory traceData exponential beta oneLink bilateral divide

  productTest : CoarseTest → CoarseTest → CoarseTest
  productTest =
    R445.sourceCoarseProduct
      theory traceData exponential beta oneLink bilateral divide

  -- Nothing physical is assumed here: this is exactly original E1A3,
  -- instantiated at the ACTUAL chosen n=3/1 fine/coarse Wilson source.
  originalE1FineBlockedIsOriginalR445Effective :
    ∀ test →
    originalE1FineBlocked test ≡ originalR445Effective test
  originalE1FineBlockedIsOriginalR445Effective =
    E1A3.originalE1FineBlockedIsR445EffectiveCoarse
      theory traceData exponential beta oneLink bilateral divide

  originalE1BareCoarseIsOriginalR445Bare :
    ∀ test →
    originalE1BareCoarse test ≡ originalR445Bare test
  originalE1BareCoarseIsOriginalR445Bare test = refl

  -- This pays the literal E1 -> R445 error INPUT conversion: any
  -- physical bound on the LHS applies to exactly the original R445
  -- effective-vs-distinct-bare moment, WITHOUT comparing Z values.
  originalE1MomentResidualIsR445MomentResidual :
    ∀ test →
    (originalE1FineBlocked test -ℝ originalE1BareCoarse test)
    ≡
    (originalR445Effective test -ℝ originalR445Bare test)
  originalE1MomentResidualIsR445MomentResidual test =
    cong₂ _-ℝ_
      (originalE1FineBlockedIsOriginalR445Effective test)
      (originalE1BareCoarseIsOriginalR445Bare test)

  record OriginalE1ThreeMomentSameSource
      (left right : CoarseTest) : Set where
    field
      leftSame :
        (originalE1FineBlocked left -ℝ originalE1BareCoarse left)
        ≡
        (originalR445Effective left -ℝ originalR445Bare left)
      rightSame :
        (originalE1FineBlocked right -ℝ originalE1BareCoarse right)
        ≡
        (originalR445Effective right -ℝ originalR445Bare right)
      productSame :
        (originalE1FineBlocked (productTest left right)
          -ℝ originalE1BareCoarse (productTest left right))
        ≡
        (originalR445Effective (productTest left right)
          -ℝ originalR445Bare (productTest left right))

  -- THREE exact source identities at once: F, G AND FG. This does not
  -- claim the three numerical errors are small; the source estimates
  -- remain a physical Wilson RG task.
  originalE1ThreeMomentSameSource :
    ∀ left right → OriginalE1ThreeMomentSameSource left right
  originalE1ThreeMomentSameSource left right = record
    { OriginalE1ThreeMomentSameSource.leftSame =
        originalE1MomentResidualIsR445MomentResidual left
    ; OriginalE1ThreeMomentSameSource.rightSame =
        originalE1MomentResidualIsR445MomentResidual right
    ; OriginalE1ThreeMomentSameSource.productSame =
        originalE1MomentResidualIsR445MomentResidual
          (productTest left right)
    }

  originalE1FineBlockedCovariance : CoarseTest → CoarseTest → ℝ
  originalE1FineBlockedCovariance left right =
    originalE1FineBlocked (productTest left right)
    -ℝ
      (originalE1FineBlocked left *ℝ originalE1FineBlocked right)

  originalR445EffectiveCovariance : CoarseTest → CoarseTest → ℝ
  originalR445EffectiveCovariance =
    R445.sourceEffectiveCovariance
      theory traceData exponential beta oneLink bilateral divide

  originalR445BareCovariance : CoarseTest → CoarseTest → ℝ
  originalR445BareCovariance =
    R445.sourceBareCovariance
      theory traceData exponential beta oneLink bilateral divide

  originalE1FineBlockedCovarianceIsR445Effective :
    ∀ left right →
    originalE1FineBlockedCovariance left right
      ≡ originalR445EffectiveCovariance left right
  originalE1FineBlockedCovarianceIsR445Effective left right =
    cong₂ _-ℝ_
      (originalE1FineBlockedIsOriginalR445Effective
        (productTest left right))
      (cong₂ _*ℝ_
        (originalE1FineBlockedIsOriginalR445Effective left)
        (originalE1FineBlockedIsOriginalR445Effective right))

  originalE1FineMinusBareCovarianceIsR445Error :
    ∀ left right →
    (originalE1FineBlockedCovariance left right
      -ℝ originalR445BareCovariance left right)
    ≡
    (originalR445EffectiveCovariance left right
      -ℝ originalR445BareCovariance left right)
  originalE1FineMinusBareCovarianceIsR445Error left right =
    cong₂ _-ℝ_
      (originalE1FineBlockedCovarianceIsR445Effective left right)
      refl

  -- The actual source three-moment inequality is now accepted as
  -- input directly on E1's two different ORIGINAL cutoffs, rather
  -- than on an arbitrarily chosen probability-law or RG oracle.
  originalE1CovarianceErrorFromThreePhysicalCutoffMoments :
    (left right : CoarseTest)
    (errorProduct errorLeft errorRight
     boundEffectiveRight boundBareLeft : ℝ) →
    0ℝ ≤ℝ errorLeft →
    0ℝ ≤ℝ boundEffectiveRight →
    0ℝ ≤ℝ boundBareLeft →
    0ℝ ≤ℝ errorRight →
    absℝ
      (originalE1FineBlocked (productTest left right)
        -ℝ originalE1BareCoarse (productTest left right))
      ≤ℝ errorProduct →
    absℝ
      (originalE1FineBlocked left -ℝ originalE1BareCoarse left)
      ≤ℝ errorLeft →
    absℝ (originalR445Effective right) ≤ℝ boundEffectiveRight →
    absℝ (originalR445Bare left) ≤ℝ boundBareLeft →
    absℝ
      (originalE1FineBlocked right -ℝ originalE1BareCoarse right)
      ≤ℝ errorRight →
    absℝ
      (originalE1FineBlockedCovariance left right
        -ℝ originalR445BareCovariance left right)
      ≤ℝ
        errorProduct +ℝ
          ((errorLeft *ℝ boundEffectiveRight)
            +ℝ (boundBareLeft *ℝ errorRight))
  originalE1CovarianceErrorFromThreePhysicalCutoffMoments
      left right errP errL errR maxER maxBL
      errLNN maxERNN maxBLNN errRNN
      productError leftError rightSize leftSize rightError =
    subst
      (λ value →
        absℝ value ≤ℝ
          (errP +ℝ
            ((errL *ℝ maxER) +ℝ (maxBL *ℝ errR))))
      (sym
        (originalE1FineMinusBareCovarianceIsR445Error left right))
      (Quant.originalR445CovarianceErrorFromThreeSourceMoments
        theory traceData exponential beta oneLink bilateral divide
        left right errP errL errR maxER maxBL
        errLNN maxERNN maxBLNN errRNN
        (subst
          (λ value → absℝ value ≤ℝ errP)
          (originalE1MomentResidualIsR445MomentResidual
            (productTest left right))
          productError)
        (subst
          (λ value → absℝ value ≤ℝ errL)
          (originalE1MomentResidualIsR445MomentResidual left)
          leftError)
        rightSize leftSize
        (subst
          (λ value → absℝ value ≤ℝ errR)
          (originalE1MomentResidualIsR445MomentResidual right)
          rightError))
