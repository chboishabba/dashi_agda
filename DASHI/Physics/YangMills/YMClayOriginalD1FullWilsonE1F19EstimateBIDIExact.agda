module DASHI.Physics.YangMills.YMClayOriginalD1FullWilsonE1F19EstimateBIDIExact where

------------------------------------------------------------------------
-- P0 WELD-FORWARD: Existing FULL original Wilson small+large-field D1
-- estimate -> SAME actual native E1 cutoff-3 -> SAME F19 weighted
-- effective covariance.  No NEW decay lemma, action, field, metric,
-- Wilson bound, normalization, scalar socket, or physical clock.
--
-- ORIGINAL master estimate already owns:
--   YMClayD1OriginalFullWilsonSmallLargeFieldExact
--     .originalFullWilsonUniformGeometricClustering.
-- It is a genuine all-cutoff theorem ONCE its source record supplies
--  (A) full interacting Wilson covariance <= CMP116 small + large;
--  (B) source CMP116 selected analytic localization/compatibility;
--  (C) actual uniform large-field rate and physical distance/units.
--
-- ORIGINAL master source identity already owns:
--   YMClayOriginalVariableWilsonCovarianceSourceExact
--     .originalWilsonExpectationExtensional
--     .actualE1D1SameWilsonConnectedCovariance
-- on the literal SAME changing-cutoff SU(N) Wilson Gibbs measure.
--
-- NEW #1536 E1/F19 original source already owns:
--   .originalE1Cutoff3ConnectedCovarianceIsOriginalF19Effective,
-- following its finite actual 1024-link F19 native R445 weighted
-- normalization and E1 cutoff-3 original measure.
--
-- The only extra source selection required here is POINTWISE matching
-- of the selected D1 full-Wilson test family at cutoff 3 with the
-- actual native R445 two-link pullbacks of original coarse F,G.
-- These are observable identities, NOT an extra covariance bound or
-- independent expected value. No funext.
--
-- SOURCE-WRITTEN only: pinned Agda kernel unavailable. The physical
-- D1 record is NOT automatically inhabited by a generic CMP116 bound.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans; subst)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_; _-ℝ_; absℝ; _≤ℝ_)

import Data.Vec.Base as Vec
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as Native
import DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact as Wilson
import DASHI.Physics.YangMills.YMClayD1OriginalFullWilsonSmallLargeFieldExact as D1
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.YMClayOriginalE1A3NativeF19WeightedBIDIExact as E1F19

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

  CoarseTest : Set
  CoarseTest = Vec.Vec Link 64 → ℝ

  -- SAME original Wilson n=3 finite field and two-link block; all 896
  -- spectator links remain in the original full Gibbs integration.
  originalNativeWilsonMark :
    CoarseTest →
    Wilson.Test theory traceData exponential beta oneLink
      bilateral divide 3
  originalNativeWilsonMark observable fine =
    observable (Codec.encodeOriginalBonds 2
      (Native.nativeSUNBlockLinks {m = 1} {l = 1} theory fine))

  -- Already ORIGINAL E1/D1 share the same physical Wilson Gibbs
  -- numerator and partition. This is source-definition normalization,
  -- NOT a claimed n=3 effective==n=1 bare coarse equality.
  originalNativeWilsonCutoff3CovarianceIsE1 :
    ∀ left right →
    Wilson.originalWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide
      3 (originalNativeWilsonMark left)
        (originalNativeWilsonMark right)
    ≡
    E1F19.originalE1Cutoff3FineCovariance
      theory traceData exponential beta oneLink bilateral divide
      ordered left right
  originalNativeWilsonCutoff3CovarianceIsE1 left right = refl

  -- Reuse the physically meaningful ORIGINAL selected full Wilson
  -- cutoff-uniform small+large-field theorem; source n=3 tests must be
  -- pointwise the actual native blocked F/G, nothing more.
  record SelectedOriginalD1FullWilsonForNativeF19
      (Test Scale Volume Root J : Set)
      (source : CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root J ℝ)
      : Set₁ where
    field
      fullWilson :
        D1.OriginalSmallLargePhysicalSource
          theory traceData exponential beta oneLink bilateral divide
          Test Scale Volume Root J source

      left right : Test
      leftCoarse rightCoarse : CoarseTest

      originalLeftIsNativeR445Mark :
        ∀ fine →
        D1.physicalTest fullWilson 3 left fine
          ≡ originalNativeWilsonMark leftCoarse fine

      originalRightIsNativeR445Mark :
        ∀ fine →
        D1.physicalTest fullWilson 3 right fine
          ≡ originalNativeWilsonMark rightCoarse fine

  open SelectedOriginalD1FullWilsonForNativeF19 public

  -- Equality of original covariance from genuine source TEST
  -- identities, via already original Wilson integral congruence.
  -- This is NOT an assumption Cov_D1=Cov_E1 and is NOT a replacement
  -- finite model.
  originalD1SelectedCovarianceIsNativeWilson :
    ∀ {Test Scale Volume Root J}
      {source : CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root J ℝ}
      (selected : SelectedOriginalD1FullWilsonForNativeF19
        Test Scale Volume Root J source) →
    Wilson.originalWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide
      3 (D1.physicalTest (fullWilson selected) 3 (left selected))
        (D1.physicalTest (fullWilson selected) 3 (right selected))
    ≡
    Wilson.originalWilsonConnectedCovariance
      theory traceData exponential beta oneLink bilateral divide
      3 (originalNativeWilsonMark (leftCoarse selected))
        (originalNativeWilsonMark (rightCoarse selected))
  originalD1SelectedCovarianceIsNativeWilson selected =
    let
      sameLeft = originalLeftIsNativeR445Mark selected
      sameRight = originalRightIsNativeR445Mark selected
      sourceExt = Wilson.originalWilsonExpectationExtensional
        theory traceData exponential beta oneLink bilateral divide
      leftTest =
        D1.physicalTest (fullWilson selected) 3 (left selected)
      rightTest =
        D1.physicalTest (fullWilson selected) 3 (right selected)
      nativeLeft = originalNativeWilsonMark (leftCoarse selected)
      nativeRight = originalNativeWilsonMark (rightCoarse selected)
    in
    cong₂ _-ℝ_
      (sourceExt 3
        (λ fine → leftTest fine *ℝ rightTest fine)
        (λ fine → nativeLeft fine *ℝ nativeRight fine)
        (λ fine → cong₂ _*ℝ_ (sameLeft fine) (sameRight fine)))
      (cong₂ _*ℝ_
        (sourceExt 3 leftTest nativeLeft sameLeft)
        (sourceExt 3 rightTest nativeRight sameRight))

  -- The original FULL Wilson D1 estimate, including large fields,
  -- is now the SAME finite source bound for the F19 effective
  -- connected covariance at cutoff 3. This does not supply its
  -- source record or extend the cutoff-3 F19 map to all k.
  originalF19EffectiveCovarianceFromFullWilsonD1 :
    ∀ {Test Scale Volume Root J}
      {source : CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root J ℝ}
      (selected : SelectedOriginalD1FullWilsonForNativeF19
        Test Scale Volume Root J source) →
    absℝ
      (E1F19.originalF19EffectiveCovariance
        theory traceData exponential beta oneLink bilateral divide
        ordered (leftCoarse selected) (rightCoarse selected))
    ≤ℝ
    (D1.smallAmplitude (fullWilson selected)
      D1.+ℝ
     D1.largeAmplitude (fullWilson selected)) *ℝ
    D1.pow (D1.commonQ (fullWilson selected))
      (D1.physicalBlockDistance (fullWilson selected)
        (left selected) (right selected))
  originalF19EffectiveCovarianceFromFullWilsonD1 selected =
    let
      full = fullWilson selected
      physicalBound =
        D1.originalFullWilsonUniformGeometricClustering
          theory traceData exponential beta oneLink bilateral divide
          full 3 (left selected) (right selected)
      d1IsNative =
        originalD1SelectedCovarianceIsNativeWilson selected
      nativeIsE1 =
        originalNativeWilsonCutoff3CovarianceIsE1
          (leftCoarse selected) (rightCoarse selected)
      e1IsF19 =
        E1F19.originalE1Cutoff3ConnectedCovarianceIsOriginalF19Effective
          theory traceData exponential beta oneLink bilateral divide
          ordered (leftCoarse selected) (rightCoarse selected)
    in
    subst (λ covariance →
      absℝ covariance ≤ℝ
      (D1.smallAmplitude full D1.+ℝ D1.largeAmplitude full) *ℝ
       D1.pow (D1.commonQ full)
         (D1.physicalBlockDistance full
           (left selected) (right selected)))
      (trans d1IsNative (trans nativeIsE1 e1IsF19))
      physicalBound

-- All original D1/CMP116 W1/W3 producers remain source-owned;
-- they are not reconstructed here. Kernel and physical record
-- inhabitance are separate checks; all-cutoff E1/D2/G1 still OPEN.
