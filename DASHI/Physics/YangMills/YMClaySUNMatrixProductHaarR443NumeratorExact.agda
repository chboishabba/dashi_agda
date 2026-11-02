{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarR443NumeratorExact where

------------------------------------------------------------------------
-- R443 -> R431: SAME SU(N) SIX-PLANE GIBBS DENSITY, PRODUCT HAAR, NUMERATOR.
--
-- Owners reused: original signed SUN bond source; literal Wilson Gibbs
-- density; one-link Fubini -> finite permutation; native positive-bond codec;
-- R443 action -> density; R431 Haar -> numerator. This source introduces
-- no independent full-lattice Haar-invariance hypothesis or alternative
-- Gibbs measure. It is an exact conditional construction.
--
-- OPEN inputs are: actual compact matrix/trace authority, genuine one-link
-- Haar/Fubini for the selected test algebra, native bond codec, integration
-- laws and original six-plane spatial C3 action invariance. This finite
-- symmetry is NOT CMP119 stress insertion, UV convergence or mass gap.
--
-- Wilson (1974); Balaban (CMP 98/99, 1985), original DASHI theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; -ℝ_; _≤ℝ_; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as ProductC3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as R443
import DASHI.Physics.YangMills.YangMillsFiniteHaarActionNumeratorInvariantRound431Exact as R431

data SpatialC3 : Set where
  c3 : SpatialC3

module _
    {Matrix Complex : Set} {N linkCount : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (codec : ProductC3.SUNNativeBondProductCodec theory linkCount)
    (divide : ℝ → ℝ → ℝ)
  where

  physicalMeasure :
    Physical.PhysicalFiniteYMMeasure
      (Native.SUNSideFourLinks N theory) ℝ
  physicalMeasure =
    Gibbs.nativeSUNFiniteGibbsMeasure
      theory traceData exponential beta
      (ProductC3.nativeSUNProductIntegral oneLink codec) divide

  record PhysicalC3ActionBoundary : Set₁ where
    field
      -- This is the original literal SUN six-positive-plane action equality.
      -- A spatial C3 Wilson/trace identity on a different carrier is not enough.
      sixPlaneActionC3 : ∀ links →
        Gibbs.nativeSUNWilsonAction theory traceData beta
          (Weld.nativeForwardC3Bonds links)
        ≡ Gibbs.nativeSUNWilsonAction theory traceData beta links

      -- Reuse one-link ordered laws; all 1024-link laws are derived below.
      oneLinkOrdered : Ordered.OneLinkOrderedHaarAlgebra oneLink

      -- The existing real exponent is strictly positive. The minimal
      -- order embedding < -> <= is explicit because RealAnalysisAxioms
      -- currently exposes no strict-to-weak lemma.
      strictPositiveIsNonnegative : ∀ {value} →
        0ℝ <ℝ value → 0ℝ ≤ℝ value

  open PhysicalC3ActionBoundary public

  nativePhysicalIntegrationLaws :
    (boundary : PhysicalC3ActionBoundary) →
    Finite.PhysicalFiniteMeasureIntegrationLaws physicalMeasure
  nativePhysicalIntegrationLaws boundary = record
    { Finite.PhysicalFiniteMeasureIntegrationLaws.densityNonnegative =
        λ links →
          strictPositiveIsNonnegative boundary
            (Gibbs.nativeSUNWilsonGibbsDensityStrictlyPositive
              theory traceData exponential beta links)
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralCongruent =
        λ left right equality →
          ProductC3.productIntegralCongruent oneLink
            (λ vector → left (ProductC3.decode codec vector))
            (λ vector → right (ProductC3.decode codec vector))
            (λ vector → equality (ProductC3.decode codec vector))
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralZero =
        Ordered.productIntegralZero oneLink (oneLinkOrdered boundary)
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralAdd =
        λ left right →
          Ordered.productIntegralAdd oneLink (oneLinkOrdered boundary)
            (λ vector → left (ProductC3.decode codec vector))
            (λ vector → right (ProductC3.decode codec vector))
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralScale =
        λ scalar observable →
          Ordered.productIntegralScale oneLink (oneLinkOrdered boundary)
            scalar
            (λ vector → observable (ProductC3.decode codec vector))
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralPositive =
        λ observable pointwise →
          Ordered.productIntegralPositive oneLink (oneLinkOrdered boundary)
            (λ vector → observable (ProductC3.decode codec vector))
            (λ vector → pointwise (ProductC3.decode codec vector))
    ; Finite.PhysicalFiniteMeasureIntegrationLaws.partitionFunctionIsDensityIntegral =
        refl
    }

  nativeProductHaarR443 :
    (boundary : PhysicalC3ActionBoundary) →
    R443.WilsonGibbsHaarAction
      {Configuration = Native.SUNSideFourLinks N theory}
      {Action = SpatialC3}
      physicalMeasure (nativePhysicalIntegrationLaws boundary)
  nativeProductHaarR443 boundary = record
    { R443.WilsonGibbsHaarAction.actConfiguration =
        λ c3 links → Weld.nativeForwardC3Bonds links
    ; R443.WilsonGibbsHaarAction.actObservable =
        λ c3 observable links →
          observable (Weld.nativeForwardC3Bonds links)
    ; R443.WilsonGibbsHaarAction.observableActionIsPullback =
        λ c3 observable links → refl
    ; R443.WilsonGibbsHaarAction.finiteAction =
        Gibbs.nativeSUNWilsonAction theory traceData beta
    ; R443.WilsonGibbsHaarAction.gibbsWeight =
        λ action → Exp.expReal exponential (-ℝ action)
    ; R443.WilsonGibbsHaarAction.densityIsGibbsWeight =
        λ links → refl
    ; R443.WilsonGibbsHaarAction.finiteActionInvariant =
        λ c3 links → sixPlaneActionC3 boundary links
    ; R443.WilsonGibbsHaarAction.haarIntegralPullbackInvariant =
        λ c3 integrand →
          ProductC3.nativeSUNProductIntegralSpatialC3Invariant
            oneLink codec integrand
    }

  -- No duplicated action, density or Haar change-of-variables record.
  -- The numerator is that of the same native real SUN Gibbs measure.
  nativeProductHaarNumeratorC3 :
    (boundary : PhysicalC3ActionBoundary)
    (observable : Native.SUNSideFourLinks N theory → ℝ) →
    Finite.unnormalizedNumerator physicalMeasure
      (λ links → observable (Weld.nativeForwardC3Bonds links))
    ≡ Finite.unnormalizedNumerator physicalMeasure observable
  nativeProductHaarNumeratorC3 boundary observable =
    R431.numeratorInvariantFromHaarAndDensity
      (R443.asFiniteHaarMeasurePreservingAction
        (nativeProductHaarR443 boundary))
      c3 observable
