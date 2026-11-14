{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR443BondMarginalC3Exact where

------------------------------------------------------------------------
-- R443 -> R445: REMOVE THE AUXILIARY SITE-GAUGE COORDINATE.
--
-- Original owner: BalabanClayGate4RationalSU2BondCarrierExact has BOTH
-- links and an auxiliary siteGauge. The actual Wilson loop/action uses links,
-- not the arbitrary gauge witness. This source-written DASHI extension proves:
--
-- (1) the original six-plane Wilson deficit factors through links;
-- (2) the original C3 action descends to the bond-only carrier;
-- (3) the physical finite Haar functional can be PUSHED FORWARD along links;
-- (4) given the original R443 Gibbs identity, all integration laws and the
--     normalised expectation commute with that pushforward;
-- (5) the original R443 -> R431 finite C3 numerator theorem then applies
--     to bond-only observables, without integrating the extra gauge witness.
--
-- IMPORTANT: rational unit quaternions are NOT the full compact SU(2).
-- This is a rigorous algebraic marginalisation on the rational carrier,
-- not a construction of compact-group Haar or of the 4D continuum measure.
--
-- Sources: K. Wilson, Phys. Rev. D 10 (1974), 2445-2459,
-- DOI 10.1103/PhysRevD.10.2445; T. Balaban, CMP 99 (1985), 75-102,
-- DOI 10.1007/BF01466594. Previous DASHI R443/R431 owners retained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Q
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2AllSignedC3WilsonExact as C3
import DASHI.Physics.YangMills.YMClayR443NativeSixPlaneHaarNumeratorExact as Six
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as R443
import DASHI.Physics.YangMills.YangMillsFiniteHaarActionNumeratorInvariantRound431Exact as R431
import Data.Rational.Base using (ℚ)

BondConfiguration : Set
BondConfiguration = Native.RationalSU2BondField Weld.three

-- Canonical section fixes the auxiliary site gauge to the native identity.
-- No claim that it fixes a gauge orbit or computes a Faddeev-Popov factor.
fromBonds : BondConfiguration → Six.NativeConfiguration
fromBonds bonds = record
  { Native.RationalSU2BondData.links = bonds
  ; Native.RationalSU2BondData.siteGauge =
      λ _ → Q.identityRationalSU2
  }

forgetGauge : Six.NativeConfiguration → BondConfiguration
forgetGauge = Native.links

forgetAfterSection : ∀ bonds → forgetGauge (fromBonds bonds) ≡ bonds
forgetAfterSection bonds = refl

-- The Wilson action and EVERY native signed holonomy depend on bondField.
-- The realization's gauge component only supplies covariance witnesses.
sixDeficitOnBonds : BondConfiguration → ℚ
sixDeficitOnBonds bonds = Six.nativeSixWilsonDeficit (fromBonds bonds)

sixDeficitFactorsThroughBonds :
  ∀ configuration →
  Six.nativeSixWilsonDeficit configuration
  ≡ sixDeficitOnBonds (forgetGauge configuration)
sixDeficitFactorsThroughBonds configuration = refl

bondC3 : BondConfiguration → BondConfiguration
bondC3 = Weld.nativeForwardC3Bonds

forgetC3CommutingSquare :
  ∀ configuration →
  forgetGauge (C3.c3NativeData configuration)
  ≡ bondC3 (forgetGauge configuration)
forgetC3CommutingSquare configuration = refl

bondSixDeficitC3 :
  ∀ bonds →
  sixDeficitOnBonds (bondC3 bonds) ≡ sixDeficitOnBonds bonds
bondSixDeficitC3 bonds =
  Six.nativeSixWilsonDeficitC3 (fromBonds bonds)

-- The marginal's Haar functional is the original integration applied to a
-- pullback. It is NOT claimed to equal compact SU(2) product Haar.
bondMarginal :
  (measure : Physical.PhysicalFiniteYMMeasure Six.NativeConfiguration ℝ) →
  Physical.PhysicalFiniteYMMeasure BondConfiguration ℝ
bondMarginal measure = record
  { Physical.density =
      λ bonds → Physical.density measure (fromBonds bonds)
  ; Physical.haarIntegral =
      λ observable →
        Physical.haarIntegral measure
          (λ configuration → observable (forgetGauge configuration))
  ; Physical.multiply = Physical.multiply measure
  ; Physical.divide = Physical.divide measure
  ; Physical.partitionFunction = Physical.partitionFunction measure
  }

-- The SAME original Gibbs-source identity implies gauge-factorisation
-- of the density. No extra gauge-independence hypothesis is introduced.
densityFactorsThroughBonds :
  ∀ {measure laws}
    (boundary : Six.NativeSixPlaneHaarBoundary measure laws)
    configuration →
  Physical.density measure configuration
  ≡ Physical.density measure (fromBonds (forgetGauge configuration))
densityFactorsThroughBonds boundary configuration =
  trans
    (Six.gibbsIsNativeSixPlaneWilson boundary configuration)
    (sym (Six.gibbsIsNativeSixPlaneWilson boundary
      (fromBonds (forgetGauge configuration))))

-- Reuse the original linearity, positivity and partition theorems.
-- The last equality genuinely uses density factorisation; the pullback
-- alone would not justify an unchanged partition.
bondMarginalIntegrationLaws :
  ∀ {measure laws}
    (boundary : Six.NativeSixPlaneHaarBoundary measure laws) →
  Finite.PhysicalFiniteMeasureIntegrationLaws (bondMarginal measure)
bondMarginalIntegrationLaws {measure} {laws} boundary = record
  { Finite.PhysicalFiniteMeasureIntegrationLaws.densityNonnegative =
      λ bonds → Finite.densityNonnegative laws (fromBonds bonds)
  ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralCongruent =
      λ left right pointwise →
        Finite.haarIntegralCongruent laws _ _
          (λ configuration → pointwise (forgetGauge configuration))
  ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralZero =
      Finite.haarIntegralZero laws
  ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralAdd =
      λ left right → Finite.haarIntegralAdd laws _ _
  ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralScale =
      λ scalar observable → Finite.haarIntegralScale laws _ _
  ; Finite.PhysicalFiniteMeasureIntegrationLaws.haarIntegralPositive =
      λ observable pointwise →
        Finite.haarIntegralPositive laws _
          (λ configuration → pointwise (forgetGauge configuration))
  ; Finite.PhysicalFiniteMeasureIntegrationLaws.partitionFunctionIsDensityIntegral =
      trans
        (Finite.partitionFunctionIsDensityIntegral laws)
        (Finite.haarIntegralCongruent laws _ _
          (densityFactorsThroughBonds boundary))
  }

-- One physical expectation, expressed on either carrier. The proof is
-- integration congruence, not a new measure or stochastic convergence claim.
normalizedBondExpectationAgreement :
  ∀ {measure laws}
    (boundary : Six.NativeSixPlaneHaarBoundary measure laws)
    (observable : BondConfiguration → ℝ) →
  Physical.normalizedExpectation measure
    (λ configuration → observable (forgetGauge configuration))
  ≡ Physical.normalizedExpectation (bondMarginal measure) observable
normalizedBondExpectationAgreement {measure} {laws} boundary observable =
  cong
    (λ numerator →
      Physical.divide measure numerator
        (Physical.partitionFunction measure))
    (Finite.haarIntegralCongruent laws _ _
      (λ configuration →
        cong
          (λ density →
            Physical.multiply measure density
              (observable (forgetGauge configuration)))
          (densityFactorsThroughBonds boundary configuration)))

bondMarginalHaarC3 :
  ∀ {measure laws}
    (boundary : Six.NativeSixPlaneHaarBoundary measure laws)
    (integrand : BondConfiguration → ℝ) →
  Physical.haarIntegral (bondMarginal measure)
    (λ bonds → integrand (bondC3 bonds))
  ≡ Physical.haarIntegral (bondMarginal measure) integrand
bondMarginalHaarC3 boundary integrand =
  Six.selectedPhysicalHaarC3Invariant boundary
    (λ configuration → integrand (forgetGauge configuration))

bondMarginalGibbsDensity :
  ∀ {measure laws}
    (boundary : Six.NativeSixPlaneHaarBoundary measure laws)
    bonds →
  Physical.density (bondMarginal measure) bonds
  ≡ Six.gibbsWeight boundary
      (Six.rationalIntoReal boundary (sixDeficitOnBonds bonds))
bondMarginalGibbsDensity boundary bonds =
  Six.gibbsIsNativeSixPlaneWilson boundary (fromBonds bonds)

bondR443 :
  ∀ {measure laws}
    (boundary : Six.NativeSixPlaneHaarBoundary measure laws) →
  R443.WilsonGibbsHaarAction
    {Configuration = BondConfiguration}
    {Action = Six.SpatialC3Generator}
    (bondMarginal measure) (bondMarginalIntegrationLaws boundary)
bondR443 boundary = record
  { R443.WilsonGibbsHaarAction.actConfiguration =
      λ _ → bondC3
  ; R443.WilsonGibbsHaarAction.actObservable =
      λ _ observable bonds → observable (bondC3 bonds)
  ; R443.WilsonGibbsHaarAction.observableActionIsPullback =
      λ _ _ _ → refl
  ; R443.WilsonGibbsHaarAction.finiteAction =
      λ bonds → Six.rationalIntoReal boundary (sixDeficitOnBonds bonds)
  ; R443.WilsonGibbsHaarAction.gibbsWeight =
      Six.gibbsWeight boundary
  ; R443.WilsonGibbsHaarAction.densityIsGibbsWeight =
      bondMarginalGibbsDensity boundary
  ; R443.WilsonGibbsHaarAction.finiteActionInvariant =
      λ _ bonds →
        cong (Six.rationalIntoReal boundary) (bondSixDeficitC3 bonds)
  ; R443.WilsonGibbsHaarAction.haarIntegralPullbackInvariant =
      λ _ integrand → bondMarginalHaarC3 boundary integrand
  }

-- The R431 source compiler now consumes the bond-only finite measure.
-- This is stronger than a mere type-level declaration that the gauge
-- coordinate is auxiliary, but still conditional on physical Haar inputs.
bondR431NumeratorC3 :
  ∀ {measure laws}
    (boundary : Six.NativeSixPlaneHaarBoundary measure laws)
    (observable : BondConfiguration → ℝ) →
  Finite.unnormalizedNumerator (bondMarginal measure)
    (λ bonds → observable (bondC3 bonds))
  ≡ Finite.unnormalizedNumerator (bondMarginal measure) observable
bondR431NumeratorC3 boundary observable =
  R431.numeratorInvariantFromHaarAndDensity
    (R443.asFiniteHaarMeasurePreservingAction (bondR443 boundary))
    Six.c3 observable
