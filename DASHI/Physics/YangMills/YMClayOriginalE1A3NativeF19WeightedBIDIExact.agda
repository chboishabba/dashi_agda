module DASHI.Physics.YangMills.YMClayOriginalE1A3NativeF19WeightedBIDIExact where

------------------------------------------------------------------------
-- P0 STEELMAN BIDI: actual original changing-cutoff E1 n=3 finite
-- Wilson Gibbs source -> original native R445 -> original interacting
-- F19 128 pair-selected + 896 spectator effective weighted density.
--
-- REVERSE endpoint:
-- E1A3.originalE1FineBlockedExpectation f on the actual n=3
-- side-four 1024-link source, not an independently chosen measure.
--
-- FORWARD source:
-- YMClayOriginalR445NativeF19WeightedPhysicalSourceBIDIExact
--     .originalNativeR445NormalizedEqualsPhysicalF19Effective
-- generated from the original full Wilson action/partition, not
-- pure-Haar or bare-coarse Wilson at beta(1).
--
-- Same source at n=3:
-- E1 original Wilson physical finite measure n=3
--   = SUNConstructedPeriodicGaugeCodec.actualPeriodicProductMeasure
--   = original oneLink productIntegral over nativeDecode positive bonds
--   = original 1024-link vector Wilson Gibbs density and partition.
-- The original native two-link block is the SAME old SUN native block.
--
-- The sole cutoff3 vector-to-function conversion is source-owned
-- Codec.encodeOriginalBonds 2 (positive coarse bonds).
--
-- Physical outputs: one source test f; then selected F, G, FG and
-- their centered covariance from the SAME weighted original state.
-- Does not assert E1 fine effective == n=1 bare Wilson; its three
-- residuals and error budget remain the original E1/R445 owner.
-- Does not claim an all-cutoff E1 continuum/W1/W3/OS/H theorem.
--
-- SOURCE-WRITTEN; Agda compiler/kernel NOT RUN. A closed definitional
-- equality between the original vector and original E1 cutoff3
-- normalized source must actually be checked by Agda.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _-ℝ_; _+ℝ_; absℝ; _≤ℝ_)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayE1A3OriginalR445CrossCutoffSourceExact as E1A3
import DASHI.Physics.YangMills.YMClayOriginalWilsonCanonicalBlockedMarkF19Exact as F19
import DASHI.Physics.YangMills.YMClayOriginalR445NativeF19WeightedPhysicalSourceBIDIExact as Weighted
import DASHI.Physics.YangMills.YMClayE1OriginalR445ThreeMomentCutoffTransportExact as ThreeMoment

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
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  CoarseVectorTest : Set
  CoarseVectorTest = Vec.Vec Link 64 → ℝ

  -- Exact original n=1 side-two POSITIVE bond enumeration. No
  -- arbitrary coarse observable-coordinate dictionary is invented.
  coarseVectorTestAsNative :
    CoarseVectorTest →
    E1A3.CoarseTest
      theory traceData exponential beta oneLink bilateral divide
  coarseVectorTestAsNative observable coarse =
    observable (Codec.encodeOriginalBonds 2 coarse)

  -- ORIGINAL E1 cutoff3 and original complete canonical 1024-vector
  -- expectation have the SAME Wilson product-Haar density and partition.
  -- This proof is a closed source-definition reduction candidate.
  originalE1Cutoff3IsNativeR445VectorExpectation :
    ∀ observable →
    E1A3.originalE1FineBlockedExpectation
      theory traceData exponential beta oneLink bilateral divide
      (coarseVectorTestAsNative observable)
    ≡
    Weighted.originalNativeR445BlockedNormalized
      theory traceData exponential (beta 3)
      oneLink bilateral ordered divide observable
  originalE1Cutoff3IsNativeR445VectorExpectation observable = refl

  -- Actual E1 physical n=3 Wilson test on the left,
  -- original F19 interacting effective density on the right.
  -- This is the direct finite E1 source-first BIDI square, not
  -- an equality to independently bare n=1 Wilson at beta(1).
  originalE1Cutoff3NativeIsOriginalF19WeightedEffective :
    ∀ observable →
    E1A3.originalE1FineBlockedExpectation
      theory traceData exponential beta oneLink bilateral divide
      (coarseVectorTestAsNative observable)
    ≡
    F19.originalEffectiveBlockedNormalized
      theory traceData exponential (beta 3)
      oneLink bilateral ordered divide observable
  originalE1Cutoff3NativeIsOriginalF19WeightedEffective observable =
    trans
      (originalE1Cutoff3IsNativeR445VectorExpectation observable)
      (Weighted.originalNativeR445NormalizedEqualsPhysicalF19Effective
        theory traceData exponential (beta 3)
        oneLink bilateral ordered divide observable)

  -- Same original E1 positive cutoff3 state for F,G,FG.
  -- Their connected covariance is an ordinary congruence, not a
  -- second R320 scalar/measure carrier.
  originalE1Cutoff3FineCovariance :
    CoarseVectorTest → CoarseVectorTest → ℝ
  originalE1Cutoff3FineCovariance left right =
    E1A3.originalE1FineBlockedExpectation
      theory traceData exponential beta oneLink bilateral divide
      (coarseVectorTestAsNative (λ pairs → left pairs *ℝ right pairs))
    -ℝ
    (E1A3.originalE1FineBlockedExpectation
      theory traceData exponential beta oneLink bilateral divide
      (coarseVectorTestAsNative left)
      *ℝ
     E1A3.originalE1FineBlockedExpectation
      theory traceData exponential beta oneLink bilateral divide
      (coarseVectorTestAsNative right))

  originalF19EffectiveCovariance :
    CoarseVectorTest → CoarseVectorTest → ℝ
  originalF19EffectiveCovariance left right =
    F19.originalEffectiveBlockedNormalized
      theory traceData exponential (beta 3)
      oneLink bilateral ordered divide
      (λ pairs → left pairs *ℝ right pairs)
    -ℝ
    (F19.originalEffectiveBlockedNormalized
      theory traceData exponential (beta 3)
      oneLink bilateral ordered divide left
      *ℝ
     F19.originalEffectiveBlockedNormalized
      theory traceData exponential (beta 3)
      oneLink bilateral ordered divide right)

  originalE1Cutoff3ConnectedCovarianceIsOriginalF19Effective :
    ∀ left right →
    originalE1Cutoff3FineCovariance left right
      ≡ originalF19EffectiveCovariance left right
  originalE1Cutoff3ConnectedCovarianceIsOriginalF19Effective left right =
    cong₂ _-ℝ_
      (originalE1Cutoff3NativeIsOriginalF19WeightedEffective
        (λ pairs → left pairs *ℝ right pairs))
      (cong₂ _*ℝ_
        (originalE1Cutoff3NativeIsOriginalF19WeightedEffective left)
        (originalE1Cutoff3NativeIsOriginalF19WeightedEffective right))

  -- Forward next producer is ALREADY ORIGINAL E1/R445 three-moment
  -- R445 quantitative cutoff error; not a second covariance estimate.
  -- The vector-tested F,G,FG are exactly the same side-two functions
  -- admitted by this original source.
  originalE1VectorCovarianceIsOriginalThreeMomentE1 :
    ∀ left right →
    originalE1Cutoff3FineCovariance left right
      ≡ ThreeMoment.originalE1FineBlockedCovariance
          theory traceData exponential beta oneLink bilateral divide
          (coarseVectorTestAsNative left)
          (coarseVectorTestAsNative right)
  originalE1VectorCovarianceIsOriginalThreeMomentE1 left right = refl

  -- The same source triangle closes on the ORIGINAL R445 E1 effective
  -- covariance, with three-moment error transport already available.
  originalF19EffectiveCovarianceIsOriginalR445ThreeMoment :
    ∀ left right →
    originalF19EffectiveCovariance left right
      ≡ ThreeMoment.originalR445EffectiveCovariance
          theory traceData exponential beta oneLink bilateral divide
          (coarseVectorTestAsNative left)
          (coarseVectorTestAsNative right)
  originalF19EffectiveCovarianceIsOriginalR445ThreeMoment left right =
    trans
      (sym
        (originalE1Cutoff3ConnectedCovarianceIsOriginalF19Effective
          left right))
      (trans
        (originalE1VectorCovarianceIsOriginalThreeMomentE1 left right)
        (ThreeMoment.originalE1FineBlockedCovarianceIsR445Effective
          theory traceData exponential beta oneLink bilateral divide
          (coarseVectorTestAsNative left)
          (coarseVectorTestAsNative right)))

  -- A FULL three-moment original WILSON ERROR COMPILER consumed from
  -- the existing source, now with the F19 *effective* covariance as
  -- the LHS. The incoming bounds are the EXACT original E1 n=3
  -- blocked vs independently bare n=1 source F/G/FG errors.
  -- There are NO invented smallness, UV/IR or 1/k hypotheses.
  originalF19EffectiveCovarianceErrorFromE1ThreePhysicalMoments :
    (left right : CoarseVectorTest)
    (errorProduct errorLeft errorRight
     boundEffectiveRight boundBareLeft : ℝ) →
    0ℝ ≤ℝ errorLeft →
    0ℝ ≤ℝ boundEffectiveRight →
    0ℝ ≤ℝ boundBareLeft →
    0ℝ ≤ℝ errorRight →
    absℝ
      (ThreeMoment.originalE1FineBlocked
         theory traceData exponential beta oneLink bilateral divide
         (ThreeMoment.productTest
           theory traceData exponential beta oneLink bilateral divide
           (coarseVectorTestAsNative left)
           (coarseVectorTestAsNative right))
       -ℝ
       ThreeMoment.originalE1BareCoarse
         theory traceData exponential beta oneLink bilateral divide
         (ThreeMoment.productTest
           theory traceData exponential beta oneLink bilateral divide
           (coarseVectorTestAsNative left)
           (coarseVectorTestAsNative right)))
      ≤ℝ errorProduct →
    absℝ
      (ThreeMoment.originalE1FineBlocked
         theory traceData exponential beta oneLink bilateral divide
         (coarseVectorTestAsNative left)
       -ℝ
       ThreeMoment.originalE1BareCoarse
         theory traceData exponential beta oneLink bilateral divide
         (coarseVectorTestAsNative left))
      ≤ℝ errorLeft →
    absℝ
      (ThreeMoment.originalR445Effective
         theory traceData exponential beta oneLink bilateral divide
         (coarseVectorTestAsNative right))
      ≤ℝ boundEffectiveRight →
    absℝ
      (ThreeMoment.originalR445Bare
         theory traceData exponential beta oneLink bilateral divide
         (coarseVectorTestAsNative left))
      ≤ℝ boundBareLeft →
    absℝ
      (ThreeMoment.originalE1FineBlocked
         theory traceData exponential beta oneLink bilateral divide
         (coarseVectorTestAsNative right)
       -ℝ
       ThreeMoment.originalE1BareCoarse
         theory traceData exponential beta oneLink bilateral divide
         (coarseVectorTestAsNative right))
      ≤ℝ errorRight →
    absℝ
      (originalF19EffectiveCovariance left right -ℝ
       ThreeMoment.originalR445BareCovariance
         theory traceData exponential beta oneLink bilateral divide
         (coarseVectorTestAsNative left)
         (coarseVectorTestAsNative right))
      ≤ℝ
      (errorProduct +ℝ
        ((errorLeft *ℝ boundEffectiveRight)
          +ℝ (boundBareLeft *ℝ errorRight)))
  originalF19EffectiveCovarianceErrorFromE1ThreePhysicalMoments
      left right errP errL errR maxER maxBL
      errLNN maxERNN maxBLNN errRNN
      productError leftError rightSize leftSize rightError =
    let
      sourceLeft = coarseVectorTestAsNative left
      sourceRight = coarseVectorTestAsNative right
      rate = errP +ℝ
        ((errL *ℝ maxER) +ℝ (maxBL *ℝ errR))
      originalBare =
        ThreeMoment.originalR445BareCovariance
          theory traceData exponential beta oneLink bilateral divide
          sourceLeft sourceRight
      samePhysicalCovariance =
        trans
          (sym
            (originalE1Cutoff3ConnectedCovarianceIsOriginalF19Effective
              left right))
          (originalE1VectorCovarianceIsOriginalThreeMomentE1 left right)
    in
    subst
      (λ effective →
        absℝ (effective -ℝ originalBare) ≤ℝ rate)
      (sym samePhysicalCovariance)
      (ThreeMoment.originalE1CovarianceErrorFromThreePhysicalCutoffMoments
        theory traceData exponential beta oneLink bilateral divide
        sourceLeft sourceRight errP errL errR maxER maxBL
        errLNN maxERNN maxBLNN errRNN
        productError leftError rightSize leftSize rightError)

  -- Original E1 at n=1 is the *different* independently bare Wilson
  -- measure, whose three F/G/FG comparison errors are already owned by
  -- ThreeMoment.originalE1CovarianceErrorFromThreePhysicalCutoffMoments.
  -- We do NOT replace that source by the n=3 F19 effective density.

