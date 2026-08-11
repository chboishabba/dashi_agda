module DASHI.Physics.Closure.NSTriadKNLuoLocalizedProjectedKornAffineCounterexampleExact where

------------------------------------------------------------------------
-- PRIMARY AUDIT TARGET
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- The manuscript's localized projected Korn claim is
--
--   integral_Omega |Pi+ grad u|^2
--     <= C_Omega integral_Omega |grad S(u)|^2
--
-- for every divergence-free H2 field on a bounded Lipschitz domain.
--
-- DASHI CONTRIBUTION
--
-- On the unit cube take the affine divergence-free field
--
--   u(x,y,z) = (2x,-y,-z).
--
-- Its gradient and strain are the constant trace-free matrix
-- diag(2,-1,-1).  Hence grad S = 0, while projection onto the positive
-- eigenspace retains the first row of the gradient and has squared
-- Frobenius mass 4.  The positive-strain contraction is 8.  Therefore every
-- proposed finite coefficient multiplies a zero right-hand side and the
-- claimed localized estimate fails strictly.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _<_; positive)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoPositiveStrainGradientSignExact as Sign

unitCubeVolume : ℚ
unitCubeVolume = 1ℚ

affineGradient : Sign.Matrix3
affineGradient =
  Sign.matrix3
    2 0ℚ 0ℚ
    0ℚ (- 1ℚ) 0ℚ
    0ℚ 0ℚ (- 1ℚ)

affineDivergence : ℚ
affineDivergence =
  Sign.a11 affineGradient
  + Sign.a22 affineGradient
  + Sign.a33 affineGradient

affineDivergenceFree : affineDivergence ≡ 0ℚ
affineDivergenceFree = solve []

positiveSpectralProjector : Sign.Matrix3
positiveSpectralProjector =
  Sign.matrix3
    1ℚ 0ℚ 0ℚ
    0ℚ 0ℚ 0ℚ
    0ℚ 0ℚ 0ℚ

projectedGradientFrobeniusSquared : ℚ
projectedGradientFrobeniusSquared =
  unitCubeVolume *
    ( Sign.a11 affineGradient * Sign.a11 affineGradient
    + Sign.a12 affineGradient * Sign.a12 affineGradient
    + Sign.a13 affineGradient * Sign.a13 affineGradient
    )

projectedGradientMassIsFour :
  projectedGradientFrobeniusSquared ≡ 4
projectedGradientMassIsFour = solve []

positiveStrainContraction : ℚ
positiveStrainContraction =
  unitCubeVolume *
    ( 2 * Sign.a11 affineGradient * Sign.a11 affineGradient )

positiveStrainContractionIsEight :
  positiveStrainContraction ≡ 8
positiveStrainContractionIsEight = solve []

strainDerivativeSquared : ℚ
strainDerivativeSquared = 0ℚ

strainDerivativeVanishes : strainDerivativeSquared ≡ 0ℚ
strainDerivativeVanishes = solve []

fourPositive : 0ℚ < 4
fourPositive = ℚₚ.positive⁻¹ 4

eightPositive : 0ℚ < 8
eightPositive = ℚₚ.positive⁻¹ 8

projectedKornRightHandSideVanishes :
  ∀ coefficient →
  coefficient * strainDerivativeSquared ≡ 0ℚ
projectedKornRightHandSideVanishes coefficient =
  solve (coefficient ∷ [])

localizedProjectedKornFailsForEveryCoefficient :
  ∀ coefficient →
  coefficient * strainDerivativeSquared
  < projectedGradientFrobeniusSquared
localizedProjectedKornFailsForEveryCoefficient coefficient =
  subst
    (λ left → left < projectedGradientFrobeniusSquared)
    (sym (projectedKornRightHandSideVanishes coefficient))
    (subst
      (λ right → 0ℚ < right)
      (sym projectedGradientMassIsFour)
      fourPositive)

positiveStrainLaplacianSurrogateFailsForEveryCoefficient :
  ∀ coefficient →
  coefficient * strainDerivativeSquared
  < positiveStrainContraction
positiveStrainLaplacianSurrogateFailsForEveryCoefficient coefficient =
  subst
    (λ left → left < positiveStrainContraction)
    (sym (projectedKornRightHandSideVanishes coefficient))
    (subst
      (λ right → 0ℚ < right)
      (sym positiveStrainContractionIsEight)
      eightPositive)

record AffineProjectedKornAudit : Set where
  constructor affineProjectedKornAudit
  field
    divergenceFree : affineDivergence ≡ 0ℚ
    positiveProjectionNonzero : 0ℚ < projectedGradientFrobeniusSquared
    strainGradientZero : strainDerivativeSquared ≡ 0ℚ

canonicalAffineProjectedKornAudit : AffineProjectedKornAudit
canonicalAffineProjectedKornAudit =
  affineProjectedKornAudit
    affineDivergenceFree
    (subst
      (λ right → 0ℚ < right)
      (sym projectedGradientMassIsFour)
      fourPositive)
    strainDerivativeVanishes
