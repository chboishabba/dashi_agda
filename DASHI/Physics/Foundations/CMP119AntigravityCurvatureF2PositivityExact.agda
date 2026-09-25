{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCurvatureF2PositivityExact where

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; NonNegative; nonNegative; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Curvature
import DASHI.Physics.Foundations.CMP119AntigravityFiniteHaarStrictPositivityExact as Strict
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact as Curl

------------------------------------------------------------------------
-- SIX-CURVATURE F^2 POSITIVITY
--
-- With E_ab = (1/2)<F_ab,F_ab>, define the normalized six-curvature F^2
-- observable by the sum of the six E_ab.  Any conventional overall positive
-- factor (including 2 or 1/pi^2) must be attached explicitly elsewhere.
--
-- Rational square positivity makes every E_ab nonnegative.  A single strictly
-- positive component energy makes the full sum strictly positive.
------------------------------------------------------------------------

vectorNormSqNonnegative :
  (value : Curl.RationalVector3) →
  0ℚ ≤ Curl.vectorNormSq value
vectorNormSqNonnegative (Curl.vec3 x y z) =
  let
    instance
      xNN : NonNegative (x * x)
      xNN = nonNegative (ℚP.nonNegative⁻¹ (x * x))

      yNN : NonNegative (y * y)
      yNN = nonNegative (ℚP.nonNegative⁻¹ (y * y))

      zNN : NonNegative (z * z)
      zNN = nonNegative (ℚP.nonNegative⁻¹ (z * z))
  in
  ℚP.nonNegative⁻¹ _

halfPositive : 0ℚ < Curvature.half
halfPositive = ℚP.positive⁻¹ Curvature.half

energyNonnegative :
  (value : Curl.RationalVector3) →
  0ℚ ≤ Curvature.energy value
energyNonnegative (Curl.vec3 x y z) =
  let
    instance
      halfNN : NonNegative Curvature.half
      halfNN = nonNegative (ℚP.<⇒≤ halfPositive)

      xNN : NonNegative (x * x)
      xNN = nonNegative (ℚP.nonNegative⁻¹ (x * x))

      yNN : NonNegative (y * y)
      yNN = nonNegative (ℚP.nonNegative⁻¹ (y * y))

      zNN : NonNegative (z * z)
      zNN = nonNegative (ℚP.nonNegative⁻¹ (z * z))

      normNN : NonNegative
        (x * x + y * y + z * z)
      normNN = nonNegative
        (ℚP.+-mono-≤
          (ℚP.nonNegative⁻¹ (x * x))
          (ℚP.+-mono-≤
            (ℚP.nonNegative⁻¹ (y * y))
            (ℚP.nonNegative⁻¹ (z * z))))
  in
  ℚP.nonNegative⁻¹ _

normalizedCurvatureF2 :
  Curvature.CurvatureSix → ℚ
normalizedCurvatureF2 curvature =
  Curvature.energy (Curvature.f01 curvature)
  + Curvature.energy (Curvature.f02 curvature)
  + Curvature.energy (Curvature.f03 curvature)
  + Curvature.energy (Curvature.f12 curvature)
  + Curvature.energy (Curvature.f13 curvature)
  + Curvature.energy (Curvature.f23 curvature)

normalizedCurvatureF2Nonnegative :
  (curvature : Curvature.CurvatureSix) →
  0ℚ ≤ normalizedCurvatureF2 curvature
normalizedCurvatureF2Nonnegative curvature =
  ℚP.+-mono-≤
    (energyNonnegative (Curvature.f01 curvature))
    (ℚP.+-mono-≤
      (energyNonnegative (Curvature.f02 curvature))
      (ℚP.+-mono-≤
        (energyNonnegative (Curvature.f03 curvature))
        (ℚP.+-mono-≤
          (energyNonnegative (Curvature.f12 curvature))
          (ℚP.+-mono-≤
            (energyNonnegative (Curvature.f13 curvature))
            (energyNonnegative (Curvature.f23 curvature))))))

record PositiveCurvatureEnergyWitness
    (curvature : Curvature.CurvatureSix) : Set where
  field
    positiveF01 :
      Positive (Curvature.energy (Curvature.f01 curvature))

open PositiveCurvatureEnergyWitness public

normalizedCurvatureF2PositiveFromF01 :
  ∀ {curvature} →
  PositiveCurvatureEnergyWitness curvature →
  0ℚ < normalizedCurvatureF2 curvature
normalizedCurvatureF2PositiveFromF01 {curvature} witness =
  let
    tailNN :
      0ℚ ≤
        Curvature.energy (Curvature.f02 curvature)
        + Curvature.energy (Curvature.f03 curvature)
        + Curvature.energy (Curvature.f12 curvature)
        + Curvature.energy (Curvature.f13 curvature)
        + Curvature.energy (Curvature.f23 curvature)
    tailNN =
      ℚP.+-mono-≤
        (energyNonnegative (Curvature.f02 curvature))
        (ℚP.+-mono-≤
          (energyNonnegative (Curvature.f03 curvature))
          (ℚP.+-mono-≤
            (energyNonnegative (Curvature.f12 curvature))
            (ℚP.+-mono-≤
              (energyNonnegative (Curvature.f13 curvature))
              (energyNonnegative (Curvature.f23 curvature)))))
    instance
      f01Positive :
        Positive (Curvature.energy (Curvature.f01 curvature))
      f01Positive = positiveF01 witness
  in
  ℚP.+-mono-<-≤
    (ℚP.positive⁻¹
      (Curvature.energy (Curvature.f01 curvature)))
    tailNN

record FiniteCurvatureF2Family (Configuration : Set) : Set₁ where
  field
    curvature :
      Curvature.FiniteCurvatureSixFamily Configuration

open FiniteCurvatureF2Family public

fieldStrengthSquare :
  ∀ {Configuration} →
  FiniteCurvatureF2Family Configuration →
  Configuration → ℚ
fieldStrengthSquare family configuration =
  normalizedCurvatureF2
    (Curvature.curvatureAt (curvature family) configuration)

fieldStrengthSquareNonnegative :
  ∀ {Configuration}
    (family : FiniteCurvatureF2Family Configuration)
    configuration →
  0ℚ ≤ fieldStrengthSquare family configuration
fieldStrengthSquareNonnegative family configuration =
  normalizedCurvatureF2Nonnegative
    (Curvature.curvatureAt (curvature family) configuration)


------------------------------------------------------------------------
-- SELECTED FINITE-MEASURE WITNESS CONSTRUCTOR
------------------------------------------------------------------------

record SelectedCurvatureF2PositiveWitness
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (quadrature : Strict.FiniteRationalHaarQuadrature measure)
    (family : FiniteCurvatureF2Family Configuration) : Set where
  field
    positiveCurvatureAtQuadratureWitness :
      PositiveCurvatureEnergyWitness
        (Curvature.curvatureAt
          (curvature family)
          (Strict.positiveWitness quadrature))

open SelectedCurvatureF2PositiveWitness public

asPositiveFieldStrengthSquareWitness :
  ∀ {Configuration measure}
    {quadrature :
      Strict.FiniteRationalHaarQuadrature
        {Configuration = Configuration} measure}
    {family : FiniteCurvatureF2Family Configuration} →
  SelectedCurvatureF2PositiveWitness quadrature family →
  Strict.PositiveFieldStrengthSquareWitness
    quadrature
    (fieldStrengthSquare family)
asPositiveFieldStrengthSquareWitness
    {quadrature = quadrature} {family = family} witness = record
  { Strict.PositiveFieldStrengthSquareWitness.fieldStrengthSquareNonnegative =
      fieldStrengthSquareNonnegative family
  ; Strict.PositiveFieldStrengthSquareWitness.fieldStrengthSquarePositiveAtWitness =
      ℚ.positive
        (normalizedCurvatureF2PositiveFromF01
          (positiveCurvatureAtQuadratureWitness witness))
  }
