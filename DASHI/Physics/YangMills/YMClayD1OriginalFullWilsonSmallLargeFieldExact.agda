module DASHI.Physics.YangMills.YMClayD1OriginalFullWilsonSmallLargeFieldExact where

------------------------------------------------------------------------
-- CLAY D1: SMALL-FIELD CMP116 + ORIGINAL LARGE-FIELD REMAINDER.
--
-- Bałaban CMP109/CMP116 proves localized differentiated cluster
-- expansions in the small-field approximation; those estimates MUST NOT
-- be equated with the full original Wilson Gibbs response.
--
-- This theorem isolates the three actual source payments:
--   A. original full covariance vs selected small-field response/error;
--   B. selected CMP116 common analytic domain and localized small field;
--   C. uniformly controlled LARGE-FIELD remainder and physical rate.
--
-- The conclusion is a true ORIGINAL real-valued Wilson covariance
-- bound on all variable lattice sizes with a common physical cube side.
-- Neither A nor C is asserted as an established result here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; absℝ; _+ℝ_; _*ℝ_; _≤ℝ_; _<ℝ_; ≤ℝ-trans;
   +-mono-≤; *-distribʳ-+)
open import Relation.Binary.PropositionalEquality using (sym; subst)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as Wilson
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116

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

  pow : ℝ → Nat → ℝ
  pow q zero = 1ℝ
  pow q (suc n) = q *ℝ pow q n

  record OriginalSmallLargePhysicalSource
      (Test Scale Volume Root J : Set)
      (source : CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root J ℝ) : Set₁ where
    field
      physicalTest :
        (n : Nat) → Test →
        Wilson.Test theory traceData exponential beta oneLink
          bilateral divide n
      gaugeInvariant :
        ∀ n label →
        Wilson.originalGaugeInvariant
          theory traceData exponential beta oneLink bilateral divide
          n (physicalTest n label)

      scaleAt : Nat → Scale
      volumeAt : Nat → Volume
      jOf : Test → J
      admissible :
        ∀ n left right →
        CMP116.AdmissibleSourcePair source
          (scaleAt n) (volumeAt n) (jOf left) (jOf right)

      cmp116OrderIsReal :
        ∀ lower upper →
        CMP116.LessEqual source lower upper →
        lower ≤ℝ upper

      -- The true large-field remainder for the ORIGINAL full Gibbs
      -- measure. An arbitrary symbolic remainder does not pay this:
      -- the source must derive the inequality from its conditional
      -- field decomposition at each cutoff.
      largeFieldError : Nat → Test → Test → ℝ
      originalFullCovarianceBelowSmallPlusLarge :
        ∀ n left right →
        absℝ
          (Wilson.originalWilsonConnectedCovariance
            theory traceData exponential beta oneLink bilateral divide
            n (physicalTest n left) (physicalTest n right))
        ≤ℝ
        CMP116.differentiatedMagnitude source
          (scaleAt n) (volumeAt n) (jOf left) (jOf right)
          +ℝ largeFieldError n left right

      -- Physical uniform envelopes independent of cutoff/volume.
      smallFieldUpper largeFieldUpper : Test → Test → ℝ
      smallFieldEnvelopeCalibration :
        ∀ n left right →
        CMP116.sourceEnvelope source
          (scaleAt n) (volumeAt n)
          (CMP116.sourceRoot source
            (scaleAt n) (volumeAt n) (jOf left) (jOf right))
          (CMP116.sourceDistance source (jOf left) (jOf right))
        ≤ℝ smallFieldUpper left right

      largeFieldErrorCalibration :
        ∀ n left right →
        largeFieldError n left right ≤ℝ largeFieldUpper left right

      -- Both small and large contributions use the same calibrated
      -- physical-block distance, q<1, and fixed physical cube size.
      cubeLength : ℝ
      cubeLengthPositive : 0ℝ <ℝ cubeLength
      physicalBlockDistance : Test → Test → Nat
      commonQ : ℝ
      commonQNonnegative : 0ℝ ≤ℝ commonQ
      commonQStrict : commonQ <ℝ 1ℝ
      smallAmplitude largeAmplitude : ℝ
      smallAmplitudeNonnegative : 0ℝ ≤ℝ smallAmplitude
      largeAmplitudeNonnegative : 0ℝ ≤ℝ largeAmplitude

      smallFieldGeometricRate :
        ∀ left right →
        smallFieldUpper left right ≤ℝ
          smallAmplitude *ℝ pow commonQ (physicalBlockDistance left right)

      largeFieldGeometricRate :
        ∀ left right →
        largeFieldUpper left right ≤ℝ
          largeAmplitude *ℝ pow commonQ (physicalBlockDistance left right)

  open OriginalSmallLargePhysicalSource public

  originalFullRealCovarianceBelowSmallLargeEnvelopes :
    ∀ {Test Scale Volume Root J}
      {source : CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root J ℝ}
      (physical : OriginalSmallLargePhysicalSource
        Test Scale Volume Root J source) →
    ∀ n left right →
    absℝ
      (Wilson.originalWilsonConnectedCovariance
        theory traceData exponential beta oneLink bilateral divide
        n (physicalTest physical n left) (physicalTest physical n right))
    ≤ℝ
    smallFieldUpper physical left right +ℝ
      largeFieldUpper physical left right
  originalFullRealCovarianceBelowSmallLargeEnvelopes
      {source = source} physical n left right =
    ≤ℝ-trans
      (originalFullCovarianceBelowSmallPlusLarge physical n left right)
      (+-mono-≤
        (≤ℝ-trans
          (cmp116OrderIsReal physical _ _
            (CMP116.sourceDifferentiatedLocalization source
              (scaleAt physical n) (volumeAt physical n)
              (jOf physical left) (jOf physical right)
              (admissible physical n left right)))
          (smallFieldEnvelopeCalibration physical n left right))
        (largeFieldErrorCalibration physical n left right))

  -- FULL original Wilson clustering in fixed physical units, as soon
  -- as the actual large-field and original source estimates are paid.
  originalFullWilsonUniformGeometricClustering :
    ∀ {Test Scale Volume Root J}
      {source : CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root J ℝ}
      (physical : OriginalSmallLargePhysicalSource
        Test Scale Volume Root J source) →
    ∀ n left right →
    absℝ
      (Wilson.originalWilsonConnectedCovariance
        theory traceData exponential beta oneLink bilateral divide
        n (physicalTest physical n left) (physicalTest physical n right))
    ≤ℝ
    (smallAmplitude physical +ℝ largeAmplitude physical) *ℝ
      pow (commonQ physical) (physicalBlockDistance physical left right)
  originalFullWilsonUniformGeometricClustering
      physical n left right =
    let
      rate = pow (commonQ physical)
        (physicalBlockDistance physical left right)
      combined :
        absℝ
          (Wilson.originalWilsonConnectedCovariance
            theory traceData exponential beta oneLink bilateral divide
            n (physicalTest physical n left) (physicalTest physical n right))
        ≤ℝ
        smallAmplitude physical *ℝ rate
          +ℝ largeAmplitude physical *ℝ rate
      combined =
        ≤ℝ-trans
          (originalFullRealCovarianceBelowSmallLargeEnvelopes
            physical n left right)
          (+-mono-≤
            (smallFieldGeometricRate physical left right)
            (largeFieldGeometricRate physical left right))
    in
    subst
      (λ upper →
        absℝ
          (Wilson.originalWilsonConnectedCovariance
            theory traceData exponential beta oneLink bilateral divide
            n (physicalTest physical n left) (physicalTest physical n right))
        ≤ℝ upper)
      (sym (*-distribʳ-+
        (smallAmplitude physical)
        (largeAmplitude physical)
        rate))
      combined
