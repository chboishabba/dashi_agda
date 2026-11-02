{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySUNProductHaarNativeGaugeR443Exact where

------------------------------------------------------------------------
-- R443 PHYSICAL LOCAL GAUGE: ORIGINAL SU(N) WILSON AND PRODUCT HAAR.
--
-- The full Wilson action/gauge proof ALREADY belongs to
-- YMClaySUNMatrixSixPlaneGaugeInvariantExact / SUNWilsonAction.
-- Do not prove or assume it again.
--
-- Given the original native bond <-> Vec codec plus its precise
-- gauge-coordinate naturality, product Haar gauge change of variables
-- is derived via one-link left/right invariance and vector induction.
-- R443 -> R431 then proves the native gauge-invariant Gibbs numerator
-- and normalized expectation on the *same* selected finite measure.
--
-- No global gauge-Haar or new density-invariance postulate is supplied.
-- Original positive bond codec and measurable SU(N) compact one-link Haar
-- are still literal source inputs; this remains a finite theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; -ℝ_; _<ℝ_; _≤ℝ_)
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGaugeInvariantExact as Gauge
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarR443NumeratorExact as Integrated
import DASHI.Physics.YangMills.YMClayFiniteProductHaarOrderedAlgebraExact as Ordered
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as ProductC3
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as R443
import DASHI.Physics.YangMills.YangMillsFiniteHaarActionNumeratorInvariantRound431Exact as R431

module _
    {Matrix Complex : Set} {N linkCount : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (source : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (leftRight : Bilateral.OneLinkSUNBilateralHaar theory source)
    (codec : ProductC3.SUNNativeBondProductCodec theory linkCount)
    (divide : ℝ → ℝ → ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  Gamma : Set
  Gamma = Bond.PeriodicSiteGauge Weld.three Link

  nativeMeasure : Physical.PhysicalFiniteYMMeasure
      (Native.SUNSideFourLinks N theory) ℝ
  nativeMeasure =
    Gibbs.nativeSUNFiniteGibbsMeasure
      theory traceData exponential beta
      (ProductC3.nativeSUNProductIntegral source codec) divide

  record OriginalBondGaugeVectorNaturality : Set₁ where
    field
      leftFactors rightFactors : Gamma → Vec Link linkCount

      -- Only the literal original bond enumeration is required to pay
      -- this same-object property. The target inverse belongs in
      -- rightFactors, not in a separate fake gauge group action.
      nativeGaugeIsVectorGauge : ∀ gamma vector →
        Gauge.sunGaugeTransformedBonds theory
          (ProductC3.decode codec vector) gamma
        ≡
        ProductC3.decode codec
          (Bilateral.gaugeBondVector theory source leftRight
            (leftFactors gamma) (rightFactors gamma) vector)

  open OriginalBondGaugeVectorNaturality public

  nativeProductHaarGaugeInvariant :
    (weld : OriginalBondGaugeVectorNaturality) →
    ∀ gamma integrand →
    Physical.haarIntegral nativeMeasure
      (λ links →
        integrand (Gauge.sunGaugeTransformedBonds theory links gamma))
    ≡ Physical.haarIntegral nativeMeasure integrand
  nativeProductHaarGaugeInvariant weld gamma integrand =
    trans
      (ProductC3.productIntegralCongruent source _ _
        (λ vector →
          cong integrand
            (nativeGaugeIsVectorGauge weld gamma vector)))
      (Bilateral.productHaarNativeGaugeInvariant
        theory source leftRight
        (leftFactors weld gamma) (rightFactors weld gamma)
        (λ vector → integrand (ProductC3.decode codec vector)))

  nativeGaugeWilsonGibbsR443 :
    (integration : Finite.PhysicalFiniteMeasureIntegrationLaws nativeMeasure)
    (weld : OriginalBondGaugeVectorNaturality) →
    R443.WilsonGibbsHaarAction
      {Configuration = Native.SUNSideFourLinks N theory}
      {Action = Gamma}
      nativeMeasure integration
  nativeGaugeWilsonGibbsR443 integration weld = record
    { R443.WilsonGibbsHaarAction.actConfiguration =
        λ gamma links → Gauge.sunGaugeTransformedBonds theory links gamma
    ; R443.WilsonGibbsHaarAction.actObservable =
        λ gamma observable links →
          observable (Gauge.sunGaugeTransformedBonds theory links gamma)
    ; R443.WilsonGibbsHaarAction.observableActionIsPullback =
        λ gamma observable links → refl
    ; R443.WilsonGibbsHaarAction.finiteAction =
        Gibbs.nativeSUNWilsonAction theory traceData beta
    ; R443.WilsonGibbsHaarAction.gibbsWeight =
        λ action → Exp.expReal exponential (-ℝ action)
    ; R443.WilsonGibbsHaarAction.densityIsGibbsWeight =
        λ links → refl
    ; R443.WilsonGibbsHaarAction.finiteActionInvariant =
        λ gamma links →
          Gauge.sunWilsonActionGaugeInvariant
            theory traceData beta links gamma
    ; R443.WilsonGibbsHaarAction.haarIntegralPullbackInvariant =
        λ gamma integrand →
          nativeProductHaarGaugeInvariant weld gamma integrand
    }

  nativeGaugeGibbsNumeratorInvariant :
    (integration : Finite.PhysicalFiniteMeasureIntegrationLaws nativeMeasure)
    (weld : OriginalBondGaugeVectorNaturality) →
    ∀ gamma observable →
    Finite.unnormalizedNumerator nativeMeasure
      (λ links →
        observable (Gauge.sunGaugeTransformedBonds theory links gamma))
    ≡ Finite.unnormalizedNumerator nativeMeasure observable
  nativeGaugeGibbsNumeratorInvariant integration weld gamma observable =
    R431.numeratorInvariantFromHaarAndDensity
      (R443.asFiniteHaarMeasurePreservingAction
        (nativeGaugeWilsonGibbsR443 integration weld))
      gamma observable

  nativeGaugeNormalizedExpectationInvariant :
    (integration : Finite.PhysicalFiniteMeasureIntegrationLaws nativeMeasure)
    (weld : OriginalBondGaugeVectorNaturality) →
    ∀ gamma observable →
    Physical.normalizedExpectation nativeMeasure
      (λ links →
        observable (Gauge.sunGaugeTransformedBonds theory links gamma))
    ≡ Physical.normalizedExpectation nativeMeasure observable
  nativeGaugeNormalizedExpectationInvariant integration weld gamma observable =
    cong
      (λ numerator →
        divide numerator (Physical.partitionFunction nativeMeasure))
      (nativeGaugeGibbsNumeratorInvariant integration weld gamma observable)

  -- Construct the literal physical integration laws on this SAME Gibbs
  -- measure from one-link ordered Haar alone. Neither C3 nor a separate
  -- whole-lattice gauge invariant measure record is needed.
  nativeGaugePhysicalIntegrationLaws :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra source)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value) →
    Finite.PhysicalFiniteMeasureIntegrationLaws nativeMeasure
  nativeGaugePhysicalIntegrationLaws ordered strictToWeak =
    Integrated.nativePhysicalIntegrationLawsFromOneLink
      theory traceData exponential beta source codec divide
      ordered strictToWeak

  nativeGaugeR443FromOneLink :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra source)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (weld : OriginalBondGaugeVectorNaturality) →
    R443.WilsonGibbsHaarAction
      {Configuration = Native.SUNSideFourLinks N theory}
      {Action = Gamma}
      nativeMeasure (nativeGaugePhysicalIntegrationLaws ordered strictToWeak)
  nativeGaugeR443FromOneLink ordered strictToWeak weld =
    nativeGaugeWilsonGibbsR443
      (nativeGaugePhysicalIntegrationLaws ordered strictToWeak) weld

  nativeGaugeNormalizedFromOneLink :
    (ordered : Ordered.OneLinkOrderedHaarAlgebra source)
    (strictToWeak : ∀ {value} → 0ℝ <ℝ value → 0ℝ ≤ℝ value)
    (weld : OriginalBondGaugeVectorNaturality) →
    ∀ gamma observable →
    Physical.normalizedExpectation nativeMeasure
      (λ links →
        observable (Gauge.sunGaugeTransformedBonds theory links gamma))
    ≡ Physical.normalizedExpectation nativeMeasure observable
  nativeGaugeNormalizedFromOneLink ordered strictToWeak weld =
    nativeGaugeNormalizedExpectationInvariant
      (nativeGaugePhysicalIntegrationLaws ordered strictToWeak)
      weld
