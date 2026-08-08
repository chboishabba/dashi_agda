module DASHI.Physics.YangMills.BalabanP33RelaxedRadiusPrincipalChartExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the exact scalar seam between the physical inverse-link radius used by
-- the P33 gauge estimate and principal-log chart admission.  For a unit
-- rational quaternion U,
--
--   N(U^-1 - 1) = 2 (1 - q0(U)).
--
-- Hence the configured relaxed radius
--
--   N(U^-1 - 1) <= 4 rho^2,   rho = 1/8192,
--
-- implies
--
--   1 - 2 rho^2 <= q0(U),
--
-- and the left side is strictly positive.  Thus every admitted physical link
-- lies in the positive-scalar hemisphere, far from the antipodal logarithm
-- cut.  The only remaining analytic chart input is the standard Hall theorem
-- identifying that hemisphere with the selected principal image.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as Signed
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log

------------------------------------------------------------------------
-- Exact unit-quaternion defect identity.
------------------------------------------------------------------------

unitInverseDefectExpansion : ∀ value →
  Norm.normSq
    (Telescope._-q_ (Physical.quaternionConjugate value) Q.oneQ)
  ≡ Physical.quaternionNormSq value
      + 1ℚ - (+ 2 / 1) * Q.q0 value
unitInverseDefectExpansion (Q.quat q0 q1 q2 q3) =
  ℚRing.solve-∀ q0 q1 q2 q3

inverseLinkDefectSqExact : ∀ background bond →
  Norm.normSq
    (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)
  ≡ (+ 2 / 1)
      * (1ℚ - Q.q0 (Physical.link background bond))
inverseLinkDefectSqExact background bond =
  let
    value = Physical.link background bond
  in
  trans
    (unitInverseDefectExpansion value)
    (trans
      (cong
        (λ selectedNorm →
          selectedNorm + 1ℚ - (+ 2 / 1) * Q.q0 value)
        (Physical.unitNorm background bond))
      (ℚRing.solve-∀ (Q.q0 value)))

------------------------------------------------------------------------
-- Configured scalar floor.
------------------------------------------------------------------------

two twoRhoSquare configuredScalarFloor : ℚ
two = + 2 / 1
twoRhoSquare = two * Signed.rhoSquare
configuredScalarFloor = 1ℚ - twoRhoSquare

twoPositiveProof : 0ℚ < two
twoPositiveProof = ℚP.positive⁻¹ two

instance
  twoPositive : Positive two
  twoPositive = ℚ.positive twoPositiveProof

fourRhoSquareIsTwoTimesTwoRhoSquare :
  Relaxed.fourRhoSquare ≡ two * twoRhoSquare
fourRhoSquareIsTwoTimesTwoRhoSquare = ℚRing.solve []

configuredScalarFloorPositive : 0ℚ < configuredScalarFloor
configuredScalarFloorPositive = ℚP.positive⁻¹ configuredScalarFloor

relaxedRadiusImpliesScalarFloor :
  ∀ background →
  Relaxed.RelaxedInverseLinkRadius background →
  ∀ bond →
  configuredScalarFloor ≤ Q.q0 (Physical.link background bond)
relaxedRadiusImpliesScalarFloor background radius bond =
  let
    scalar = Q.q0 (Physical.link background bond)

    normalizedBound :
      two * (1ℚ - scalar) ≤ Relaxed.fourRhoSquare
    normalizedBound =
      subst
        (λ lower → lower ≤ Relaxed.fourRhoSquare)
        (inverseLinkDefectSqExact background bond)
        (radius bond)

    commonScaleBound :
      two * (1ℚ - scalar) ≤ two * twoRhoSquare
    commonScaleBound =
      subst
        (λ upper → two * (1ℚ - scalar) ≤ upper)
        fourRhoSquareIsTwoTimesTwoRhoSquare
        normalizedBound

    cancelled : 1ℚ - scalar ≤ twoRhoSquare
    cancelled = ℚP.*-cancelˡ-≤-pos two commonScaleBound

    shifted :
      (1ℚ - scalar) + (scalar - twoRhoSquare)
      ≤ twoRhoSquare + (scalar - twoRhoSquare)
    shifted =
      ℚP.+-monoʳ-≤ (scalar - twoRhoSquare) cancelled
  in
  subst
    (λ lower → lower ≤ scalar)
    (ℚRing.solve-∀ scalar twoRhoSquare)
    (subst
      (λ upper →
        (1ℚ - scalar) + (scalar - twoRhoSquare) ≤ upper)
      (ℚRing.solve-∀ scalar twoRhoSquare)
      shifted)

relaxedRadiusImpliesPositiveScalarPart :
  ∀ background →
  Relaxed.RelaxedInverseLinkRadius background →
  ∀ bond →
  0ℚ < Q.q0 (Physical.link background bond)
relaxedRadiusImpliesPositiveScalarPart background radius bond =
  ℚP.<-≤-trans
    configuredScalarFloorPositive
    (relaxedRadiusImpliesScalarFloor background radius bond)

------------------------------------------------------------------------
-- Standard principal-chart recognition and physical inverse orientation.
------------------------------------------------------------------------

record RationalSU2PositiveScalarChart (Lie : Set) : Set₁ where
  field
    chart : Log.StandardSU2PrincipalLogBall
      Lie Q.RationalQuaternion ℚ

    physicalConjugateIsChartInverse : ∀ value →
      Physical.quaternionConjugate value
      ≡ Log.inverseGroup chart value

    positiveScalarInPrincipalImage : ∀ value →
      0ℚ < Q.q0 value →
      Log.InPrincipalImage chart value

open RationalSU2PositiveScalarChart public

relaxedRadiusImpliesPrincipalImage :
  ∀ {Lie}
    (recognition : RationalSU2PositiveScalarChart Lie)
    background →
  Relaxed.RelaxedInverseLinkRadius background →
  ∀ bond →
  Log.InPrincipalImage (chart recognition)
    (Physical.link background bond)
relaxedRadiusImpliesPrincipalImage recognition background radius bond =
  positiveScalarInPrincipalImage recognition
    (Physical.link background bond)
    (relaxedRadiusImpliesPositiveScalarPart background radius bond)

relaxedRadiusPhysicalInverseLogOrientation :
  ∀ {Lie}
    (recognition : RationalSU2PositiveScalarChart Lie)
    background →
  Relaxed.RelaxedInverseLinkRadius background →
  ∀ bond →
  Log.principalLog (chart recognition)
    (Physical.inverseLink background bond)
  ≡ Log.negateLie (chart recognition)
      (Log.principalLog (chart recognition)
        (Physical.link background bond))
relaxedRadiusPhysicalInverseLogOrientation
    recognition background radius bond =
  let
    value = Physical.link background bond
    admitted =
      relaxedRadiusImpliesPrincipalImage
        recognition background radius bond
  in
  trans
    (cong
      (Log.principalLog (chart recognition))
      (physicalConjugateIsChartInverse recognition value))
    (Log.principalLogOfInverse (chart recognition) value admitted)
