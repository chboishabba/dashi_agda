{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR443NativeSixPlaneHaarNumeratorExact where

------------------------------------------------------------------------
-- R443: SOURCE-SELECTED SIX-PLANE WILSON ACTION -> GIBBS/HAAR NUMERATOR.
--
-- The actual finite n=3, 4D rational-unit-SU2 bond action C3 invariance
-- is now *proved* by the preceding native reverse-path and six-plane modules.
-- This module directly attaches it to the existing R443 -> R431 physical
-- numerator compiler instead of introducing another abstract "receipt".
--
-- The two remaining data fields are genuine physical SOURCE inputs:
--  (a) Gibbs weight/density equals the selected six-plane Wilson action,
--      including proper inverse temperature and vacuum constant;
--  (b) finite compact-group product/constrained Haar under the EXACT same
--      source-selected spatial C3 configuration action.
--
-- The rational quaternion carrier alone is NOT a compact Haar SU2 theory;
-- no Haar input is manufactured here or silently inferred from cardinality.
-- No 4D Clay mass gap follows from finite C3 invariance.
--
-- Original Wilson/Balaban, R443/R431 and native SU2 owners retain credit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as R443
import DASHI.Physics.YangMills.YangMillsFiniteHaarActionNumeratorInvariantRound431Exact as R431
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2AllSignedC3WilsonExact as C3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as Six
import DASHI.Physics.YangMills.YMClayNativeSixPlaneC3ActualPhysicalSourceExact as SixC3
import Data.Rational.Base as ℚ using (ℚ)

NativeConfiguration : Set₁
NativeConfiguration = Native.RationalSU2BondData Weld.three

data SpatialC3Generator : Set where
  c3 : SpatialC3Generator

nativeC3Configuration :
  SpatialC3Generator → NativeConfiguration → NativeConfiguration
nativeC3Configuration c3 = C3.c3NativeData

nativeC3Observable :
  SpatialC3Generator →
  (NativeConfiguration → ℝ) → NativeConfiguration → ℝ
nativeC3Observable c3 observable configuration =
  observable (C3.c3NativeData configuration)

record NativeSixPlaneHaarBoundary
    (measure : Physical.PhysicalFiniteYMMeasure NativeConfiguration ℝ)
    (laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure) : Set₁ where
  field
    rationalIntoReal : ℚ → ℝ
    gibbsWeight : ℝ → ℝ

    -- Actual physical finite Wilson action/density/coupling identification.
    gibbsIsNativeSixPlaneWilson : ∀ configuration →
      Physical.density measure configuration
      ≡ gibbsWeight
          (rationalIntoReal (Six.sixPlanePhysicalTraceAction configuration))

    -- Product/constrained-Haar change of variables on SAME configuration.
    -- This is NOT delivered by a rational-point counting measure.
    selectedPhysicalHaarC3Invariant : ∀ integrand →
      Physical.haarIntegral measure
        (λ configuration → integrand (C3.c3NativeData configuration))
      ≡ Physical.haarIntegral measure integrand

open NativeSixPlaneHaarBoundary public

nativeSixPlaneR443 :
  ∀ {measure laws} →
  NativeSixPlaneHaarBoundary measure laws →
  R443.WilsonGibbsHaarAction
    {Configuration = NativeConfiguration}
    {Action = SpatialC3Generator}
    measure laws
nativeSixPlaneR443 {measure = measure} inputs = record
  { R443.WilsonGibbsHaarAction.actConfiguration =
      nativeC3Configuration
  ; R443.WilsonGibbsHaarAction.actObservable =
      nativeC3Observable
  ; R443.WilsonGibbsHaarAction.observableActionIsPullback =
      λ c3 observable configuration → refl
  ; R443.WilsonGibbsHaarAction.finiteAction =
      λ configuration →
        rationalIntoReal inputs (Six.sixPlanePhysicalTraceAction configuration)
  ; R443.WilsonGibbsHaarAction.gibbsWeight =
      gibbsWeight inputs
  ; R443.WilsonGibbsHaarAction.densityIsGibbsWeight =
      gibbsIsNativeSixPlaneWilson inputs
  ; R443.WilsonGibbsHaarAction.finiteActionInvariant =
      λ c3 configuration →
        cong (rationalIntoReal inputs)
          (SixC3.nativeSixPositiveWilsonActionSpatialC3 configuration)
  ; R443.WilsonGibbsHaarAction.haarIntegralPullbackInvariant =
      λ c3 integrand → selectedPhysicalHaarC3Invariant inputs integrand
  }

-- The numerator invariance is the ACTUAL existing R431 owner, applied
-- after R443 has consumed the SOURCE native finite Wilson action proof.
nativeSixPlaneNumeratorC3Invariant :
  ∀ {measure laws} →
  (inputs : NativeSixPlaneHaarBoundary measure laws)
  (observable : NativeConfiguration → ℝ) →
  Finite.unnormalizedNumerator measure
    (nativeC3Observable c3 observable)
  ≡ Finite.unnormalizedNumerator measure observable
nativeSixPlaneNumeratorC3Invariant inputs observable =
  R431.numeratorInvariantFromHaarAndDensity
    (R443.asFiniteHaarMeasurePreservingAction (nativeSixPlaneR443 inputs))
    c3 observable
