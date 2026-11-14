module DASHI.Physics.YangMills.YMClayOriginalWilsonNativeMarkedPushforwardExact where

------------------------------------------------------------------------
-- ORIGINAL R443 -> R445 -> R320 FULL TWO-MARKED PARTITION SOURCE.
--
-- Not merely a covariance-label equality: at the selected original
-- side-four 1024-positive-link Wilson--Gibbs measure, the entire weighted
-- two-source affine marked *partition functional* is exactly the native
-- R445 pushforward evaluated at the corresponding coarse marked
-- observable.  The partition, numerator, two marks and ordered
-- non-Abelian block are the same selected physical objects throughout.
--
-- The source is the actual complete fine WILSON GIBBS density.  The
-- pushed-forward density is its genuine effective measure and cannot
-- silently be replaced with a bare coarse Wilson action.  The further
-- identification with CMP119/CMP122 E/R/B/V/ghost/source contributions
-- and CMP116 physical localized J response is NOT manufactured here.
--
-- Coarse gauge invariance is also inherited on every composite mark
-- whose constituent coarse cylinder insertions satisfy the original
-- pointwise gauge observable contract.
--
-- No local postulates or holes; physical ℝ and selected one-link Haar
-- remain exactly the previously documented transitive inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _+ℝ_; _*ℝ_; 0ℝ; _<ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Wilson
import DASHI.Physics.YangMills.YMClayOriginalWilsonAffineMarkedPartitionExact as Affine
import DASHI.Physics.YangMills.YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact as Same
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact as Push
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedFineHaarObservableExact as Pointwise
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp

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

  FineLinks : Set
  FineLinks = Wilson.SUNPeriodicLinks theory 3

  CoarseLinks : Set
  CoarseLinks = Wilson.SUNPeriodicLinks theory 1

  actualBlock : FineLinks → CoarseLinks
  actualBlock =
    Same.originalNativeBlock
      theory traceData exponential beta oneLink bilateral divide

  originalPulledMark : (CoarseLinks → ℝ) → FineLinks → ℝ
  originalPulledMark test fine = test (actualBlock fine)

  actualCoarseAffineTest :
    (CoarseLinks → ℝ) → (CoarseLinks → ℝ) →
    ℝ → ℝ → CoarseLinks → ℝ
  actualCoarseAffineTest left right s t coarse =
    (1ℝ +ℝ s *ℝ left coarse)
    *ℝ
    (1ℝ +ℝ t *ℝ right coarse)

  actualFineWilsonMarkedPartition :
    (left right : CoarseLinks → ℝ) → ℝ → ℝ → ℝ
  actualFineWilsonMarkedPartition left right s t =
    Affine.originalAffineMarkedPartition
      theory traceData exponential beta oneLink bilateral divide
      3 (originalPulledMark left) (originalPulledMark right) s t

  actualR445PushforwardMarkedPartition :
    (left right : CoarseLinks → ℝ) → ℝ → ℝ → ℝ
  actualR445PushforwardMarkedPartition left right s t =
    Push.actualPushforwardNumerator
      theory traceData exponential (beta 3)
      oneLink bilateral divide
      (actualCoarseAffineTest left right s t)

  -- This is an ORIGINAL 1024-link weighted Gibbs identity.  It does
  -- not invoke Haar independence after turning on the interacting weight.
  fineWilsonMarkedPartitionIsNativeR445Pushforward :
    ∀ (left right : CoarseLinks → ℝ) s t →
    actualFineWilsonMarkedPartition left right s t
    ≡ actualR445PushforwardMarkedPartition left right s t
  fineWilsonMarkedPartitionIsNativeR445Pushforward left right s t = refl

  actualFineWilsonNormalizedMarked :
    (left right : CoarseLinks → ℝ) → ℝ → ℝ → ℝ
  actualFineWilsonNormalizedMarked left right s t =
    Affine.originalNormalizedAffineMarkedPartition
      theory traceData exponential beta oneLink bilateral divide
      3 (originalPulledMark left) (originalPulledMark right) s t

  actualR445PushforwardNormalizedMarked :
    (left right : CoarseLinks → ℝ) → ℝ → ℝ → ℝ
  actualR445PushforwardNormalizedMarked left right s t =
    Push.actualPushforwardNormalized
      theory traceData exponential (beta 3)
      oneLink bilateral divide
      (actualCoarseAffineTest left right s t)

  fineWilsonNormalizedMarkedIsActualR445Normalized :
    ∀ (left right : CoarseLinks → ℝ) s t →
    actualFineWilsonNormalizedMarked left right s t
    ≡ actualR445PushforwardNormalizedMarked left right s t
  fineWilsonNormalizedMarkedIsActualR445Normalized left right s t =
    refl

  -- The REAL originally selected Gibbs source also has an exact
  -- normalized two-variable MOMENT polynomial on its pushed forward
  -- cylinder test.  Reuses the previously proven full finite affine
  -- integral and the ordinary same-denominator field laws.
  originalMarkedR445IsSameFiniteMomentPolynomial :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (divideSelf : ∀ denominator →
      0ℝ <ℝ denominator → divide denominator denominator ≡ 1ℝ)
    (divideAdd : ∀ denominator →
      0ℝ <ℝ denominator → ∀ left right →
      divide (left +ℝ right) denominator
      ≡ divide left denominator +ℝ divide right denominator)
    (divideScale : ∀ denominator →
      0ℝ <ℝ denominator → ∀ scalar numerator →
      divide (scalar *ℝ numerator) denominator
      ≡ scalar *ℝ divide numerator denominator)
    (left right : CoarseLinks → ℝ) s t →
    actualR445PushforwardNormalizedMarked left right s t
    ≡ Affine.originalNormalizedMomentPolynomial
        theory traceData exponential beta oneLink bilateral divide
        3 (originalPulledMark left) (originalPulledMark right) s t
  originalMarkedR445IsSameFiniteMomentPolynomial
      ordered strictToWeak strict divideSelf divideAdd divideScale
      left right s t =
    trans
      (sym (fineWilsonNormalizedMarkedIsActualR445Normalized left right s t))
      (Affine.originalNormalizedAffineIsLiteralMomentPolynomial
        theory traceData exponential beta oneLink bilateral divide
        ordered strictToWeak strict
        divideSelf divideAdd divideScale
        3 (originalPulledMark left) (originalPulledMark right) s t)

  -- Original coarse "pointwise observable" property under an arbitrary
  -- fine-bond pointwise correspondence, which in turn already entails
  -- the true original site gauge covariance.  No gauge oracle is added.
  markedTestIsOriginalCoarsePointwise :
    (left right : CoarseLinks → ℝ)
    (leftPointwise :
      Pointwise.CoarsePointwiseObservable
        theory traceData exponential (beta 3)
        oneLink bilateral divide left)
    (rightPointwise :
      Pointwise.CoarsePointwiseObservable
        theory traceData exponential (beta 3)
        oneLink bilateral divide right)
    (s t : ℝ) →
    Pointwise.CoarsePointwiseObservable
      theory traceData exponential (beta 3)
      oneLink bilateral divide
      (actualCoarseAffineTest left right s t)
  markedTestIsOriginalCoarsePointwise
      left right leftPointwise rightPointwise s t = record
    { Pointwise.CoarsePointwiseObservable.sameAtAllBonds =
        λ first second same →
          cong₂ _*ℝ_
            (cong (λ value → 1ℝ +ℝ s *ℝ value)
              (Pointwise.sameAtAllBonds
                leftPointwise first second same))
            (cong (λ value → 1ℝ +ℝ t *ℝ value)
              (Pointwise.sameAtAllBonds
                rightPointwise first second same))
    }

  originalNativeR445MarkedSourceGaugeInvariant :
    (left right : CoarseLinks → ℝ)
    (leftPointwise :
      Pointwise.CoarsePointwiseObservable
        theory traceData exponential (beta 3)
        oneLink bilateral divide left)
    (rightPointwise :
      Pointwise.CoarsePointwiseObservable
        theory traceData exponential (beta 3)
        oneLink bilateral divide right)
    (s t : ℝ)
    (gamma : Wilson.SUNPeriodicGauge theory 1) →
    Push.actualPushforwardNormalized
      theory traceData exponential (beta 3)
      oneLink bilateral divide
      (λ coarse →
        actualCoarseAffineTest left right s t
          (Wilson.periodicSUNGaugeTransform theory 1 coarse gamma))
    ≡
    actualR445PushforwardNormalizedMarked left right s t
  originalNativeR445MarkedSourceGaugeInvariant
      left right leftPointwise rightPointwise s t gamma =
    Push.actualPushforwardAllCoarseGaugeInvariant
      theory traceData exponential (beta 3)
      oneLink bilateral divide
      (actualCoarseAffineTest left right s t)
      (markedTestIsOriginalCoarsePointwise
        left right leftPointwise rightPointwise s t)
      gamma
