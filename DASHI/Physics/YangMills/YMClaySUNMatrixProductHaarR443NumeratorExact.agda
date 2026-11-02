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
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; -ℝ_; _≤ℝ_; _<ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNMatrixSpatialC3RealFubiniExact as Spatial
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeInversePlaquetteRealTraceExact as Inverse
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact as LocalSix
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3
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
      -- Exactly the original SUN six-positive-plane local source
      -- after C3. The GLOBAL action and density invariances are DERIVED
      -- by the existing finite-monoid Fubini/sum permutation theorem.
      -- In particular this does not assume another Gibbs/action theorem.
      sixPlaneAtC3 : ∀ links site →
        Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
          (Weld.nativeForwardC3Bonds links) site
        ≡ Gibbs.nativeSUNSixWilsonDeficitAt theory traceData
            links
            (C3.spatialC3Site site)

      -- Reuse one-link ordered laws; all 1024-link laws are derived below.
      oneLinkOrdered : Ordered.OneLinkOrderedHaarAlgebra oneLink

      -- The existing real exponent is strictly positive. The minimal
      -- order embedding < -> <= is explicit because RealAnalysisAxioms
      -- currently exposes no strict-to-weak lemma.
      strictPositiveIsNonnegative : ∀ {value} →
        0ℝ <ℝ value → 0ℝ ≤ℝ value

  open PhysicalC3ActionBoundary public

  -- Construct the *remaining local source* C3 equality from native
  -- reversed ordered SU(N) holonomy plus exactly one normalized-real-trace
  -- inverse theorem. Thus no separate whole Wilson action, Gibbs density,
  -- or local six-plane invariance is left as a caller-supplied hypothesis.
  nativeC3BoundaryFromInverseTrace :
    (inverseLaw : Inverse.SUNRealTraceInverseOnNative theory traceData)
    (ordered : Ordered.OneLinkOrderedHaarAlgebra oneLink)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    PhysicalC3ActionBoundary
  nativeC3BoundaryFromInverseTrace inverseLaw ordered strictToWeak =
    record
      { PhysicalC3ActionBoundary.sixPlaneAtC3 =
          LocalSix.nativeSUNSixAtC3FromInverseRealTrace
            theory traceData inverseLaw
      ; PhysicalC3ActionBoundary.oneLinkOrdered = ordered
      ; PhysicalC3ActionBoundary.strictPositiveIsNonnegative = strictToWeak
      }

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


  -- Genuine strict positivity of the selected finite Wilson partition,
  -- provided only the one-link full-support/integrable strict positivity
  -- authority. This is not a continuum uniform lower bound.
  nativePhysicalPartitionPositive :
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink) →
    0ℝ <ℝ Physical.partitionFunction physicalMeasure
  nativePhysicalPartitionPositive strict =
    Ordered.productIntegralStrictlyPositive oneLink strict
      (λ vector →
        Gibbs.nativeSUNWilsonGibbsDensity
          theory traceData exponential beta (ProductC3.decode codec vector))
      (λ vector →
        Gibbs.nativeSUNWilsonGibbsDensityStrictlyPositive
          theory traceData exponential beta (ProductC3.decode codec vector))

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
        λ c3 links →
          Spatial.nativeSUNWilsonActionC3FromLocal
            theory traceData beta links
            (sixPlaneAtC3 boundary links)
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

  -- R431's numerator invariant is already the full finite normalized
  -- Gibbs expectation symmetry: the partition denominator is unchanged.
  -- No independent normalized-expectation C3 hypothesis is introduced.
  nativeProductHaarNormalizedC3 :
    (boundary : PhysicalC3ActionBoundary)
    (observable : Native.SUNSideFourLinks N theory → ℝ) →
    Physical.normalizedExpectation physicalMeasure
      (λ links → observable (Weld.nativeForwardC3Bonds links))
    ≡ Physical.normalizedExpectation physicalMeasure observable
  nativeProductHaarNormalizedC3 boundary observable =
    cong
      (λ numerator →
        divide numerator (Physical.partitionFunction physicalMeasure))
      (nativeProductHaarNumeratorC3 boundary observable)

  -- The same physical partition is exactly the numerator of constant one.
  -- This is an equation of the original measure record, not another law.
  nativeProductHaarUnitNumerator :
    (boundary : PhysicalC3ActionBoundary) →
    Finite.unnormalizedNumerator physicalMeasure Finite.oneObservable
    ≡ Physical.partitionFunction physicalMeasure
  nativeProductHaarUnitNumerator boundary =
    Finite.numeratorOneIsPartitionFunction
      (nativePhysicalIntegrationLaws boundary)

  -- Actual finite probability normalization. The real division field of
  -- PhysicalFiniteYMMeasure is otherwise arbitrary, so only its standard
  -- positive-self-division law is passed as a scalar input.
  nativeNormalizedWilsonUnit :
    (boundary : PhysicalC3ActionBoundary)
    (strict : Ordered.OneLinkStrictlyPositiveIntegration oneLink)
    (divideSelf : ∀ z → 0ℝ <ℝ z → divide z z ≡ 1ℝ) →
    Physical.normalizedExpectation physicalMeasure Finite.oneObservable
    ≡ 1ℝ
  nativeNormalizedWilsonUnit boundary strict divideSelf =
    trans
      (cong
        (λ numerator →
          divide numerator (Physical.partitionFunction physicalMeasure))
        (nativeProductHaarUnitNumerator boundary))
      (divideSelf (Physical.partitionFunction physicalMeasure)
        (nativePhysicalPartitionPositive strict))
