module DASHI.Physics.Closure.NSTriadKNLuoStrainSpectralRigidityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jeffrey S. Case and Aaron J. Tyrrell,
-- "A Sharp Inequality for Trace-Free Matrices with Applications to
-- Hypersurfaces".
-- DOI: 10.1090/proc/16657.
--
-- Evan Miller,
-- "A Regularity Criterion for the Navier-Stokes Equation Involving Only
-- the Middle Eigenvalue of the Strain Tensor".
-- arXiv DOI: 10.48550/arXiv.1710.05569.
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO.  DOI: none located in the public record.
-- Status: manuscript/preprint; no theorem from that manuscript is imported.
--
-- DASHI CONTRIBUTION
--
-- The trace-free three-eigenvalue algebra is proved exactly over rationals.
-- If lambda3 = -(lambda1+lambda2), Q = sum lambda_i^2 and
-- P = lambda1 lambda2 lambda3, then
--
--   Q^3 - 54 P^2
--     = 2 (lambda1-lambda2)^2
--         (lambda2-lambda3)^2
--         (lambda1-lambda3)^2 >= 0.
--
-- Since tr(S^3)=3 det(S) in dimension three for trace-free S, this yields
--
--   6 tr(S^3)^2 <= (tr(S^2))^3.
--
-- This is a sharp homogeneous cubic estimate.  It is deliberately not
-- promoted to a scale-free linear absorption of a cubic term by a quadratic
-- energy or dissipation.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

square : ℚ → ℚ
square = L2.square

cube : ℚ → ℚ
cube value = value * value * value

thirdEigenvalue : ℚ → ℚ → ℚ
thirdEigenvalue lambda1 lambda2 = - (lambda1 + lambda2)

quadraticMagnitude : ℚ → ℚ → ℚ
quadraticMagnitude lambda1 lambda2 =
  square lambda1
  + square lambda2
  + square (thirdEigenvalue lambda1 lambda2)

determinant : ℚ → ℚ → ℚ
determinant lambda1 lambda2 =
  lambda1 * lambda2 * thirdEigenvalue lambda1 lambda2

cubicTrace : ℚ → ℚ → ℚ
cubicTrace lambda1 lambda2 =
  cube lambda1
  + cube lambda2
  + cube (thirdEigenvalue lambda1 lambda2)

spectralSeparationDefect : ℚ → ℚ → ℚ
spectralSeparationDefect lambda1 lambda2 =
  2
  * square (lambda1 - lambda2)
  * square (lambda2 - thirdEigenvalue lambda1 lambda2)
  * square (lambda1 - thirdEigenvalue lambda1 lambda2)

traceFreeIdentity :
  ∀ lambda1 lambda2 →
  lambda1 + lambda2 + thirdEigenvalue lambda1 lambda2 ≡ 0ℚ
traceFreeIdentity lambda1 lambda2 = solve (lambda1 ∷ lambda2 ∷ [])

traceCubeEqualsThreeDeterminant :
  ∀ lambda1 lambda2 →
  cubicTrace lambda1 lambda2 ≡ 3 * determinant lambda1 lambda2
traceCubeEqualsThreeDeterminant lambda1 lambda2 =
  solve (lambda1 ∷ lambda2 ∷ [])

spectralRigidityIdentity :
  ∀ lambda1 lambda2 →
  cube (quadraticMagnitude lambda1 lambda2)
  ≡ 54 * square (determinant lambda1 lambda2)
    + spectralSeparationDefect lambda1 lambda2
spectralRigidityIdentity lambda1 lambda2 =
  solve (lambda1 ∷ lambda2 ∷ [])

multiplyNonnegative :
  ∀ {left right} →
  0ℚ ≤ left →
  0ℚ ≤ right →
  0ℚ ≤ left * right
multiplyNonnegative {left} {right} leftNonnegative rightNonnegative =
  let
    instance
      leftNN = nonNegative leftNonnegative
      rightNN = nonNegative rightNonnegative
      productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚₚ.nonNegative⁻¹ (left * right)

spectralSeparationDefectNonnegative :
  ∀ lambda1 lambda2 →
  0ℚ ≤ spectralSeparationDefect lambda1 lambda2
spectralSeparationDefectNonnegative lambda1 lambda2 =
  multiplyNonnegative
    (multiplyNonnegative
      (multiplyNonnegative
        (L2.squareNonnegative 2)
        (L2.squareNonnegative (lambda1 - lambda2)))
      (L2.squareNonnegative
        (lambda2 - thirdEigenvalue lambda1 lambda2)))
    (L2.squareNonnegative
      (lambda1 - thirdEigenvalue lambda1 lambda2))

sharpDeterminantBound :
  ∀ lambda1 lambda2 →
  54 * square (determinant lambda1 lambda2)
  ≤ cube (quadraticMagnitude lambda1 lambda2)
sharpDeterminantBound lambda1 lambda2 =
  let
    base = 54 * square (determinant lambda1 lambda2)
    defect = spectralSeparationDefect lambda1 lambda2

    addDefect : base ≤ base + defect
    addDefect =
      subst
        (λ lower → lower ≤ base + defect)
        (ℚₚ.+-identityʳ base)
        (ℚₚ.+-monoʳ-≤ base
          (spectralSeparationDefectNonnegative lambda1 lambda2))
  in
  subst
    (λ upper → base ≤ upper)
    (sym (spectralRigidityIdentity lambda1 lambda2))
    addDefect

sixCubicTraceSquaredEqualsFiftyFourDeterminantSquared :
  ∀ lambda1 lambda2 →
  6 * square (cubicTrace lambda1 lambda2)
  ≡ 54 * square (determinant lambda1 lambda2)
sixCubicTraceSquaredEqualsFiftyFourDeterminantSquared lambda1 lambda2 =
  solve (lambda1 ∷ lambda2 ∷ [])

sharpCubicTraceBound :
  ∀ lambda1 lambda2 →
  6 * square (cubicTrace lambda1 lambda2)
  ≤ cube (quadraticMagnitude lambda1 lambda2)
sharpCubicTraceBound lambda1 lambda2 =
  subst
    (λ lower → lower ≤ cube (quadraticMagnitude lambda1 lambda2))
    (sym
      (sixCubicTraceSquaredEqualsFiftyFourDeterminantSquared
        lambda1 lambda2))
    (sharpDeterminantBound lambda1 lambda2)

extensionalQuadraticMagnitude :
  ∀ scale →
  quadraticMagnitude (2 * scale) (- scale)
  ≡ 6 * square scale
extensionalQuadraticMagnitude scale = solve (scale ∷ [])

extensionalDeterminant :
  ∀ scale →
  determinant (2 * scale) (- scale)
  ≡ 2 * cube scale
extensionalDeterminant scale = solve (scale ∷ [])

extensionalCubicTrace :
  ∀ scale →
  cubicTrace (2 * scale) (- scale)
  ≡ 6 * cube scale
extensionalCubicTrace scale = solve (scale ∷ [])

extensionalSpectralDefectVanishes :
  ∀ scale →
  spectralSeparationDefect (2 * scale) (- scale) ≡ 0ℚ
extensionalSpectralDefectVanishes scale = solve (scale ∷ [])

record SpectralRigidityAuthorityBoundary : Set where
  constructor spectralRigidityAuthorityBoundary
  field
    sharpHomogeneousCubicBoundProved : Set
    scaleFreeCubicByQuadraticAbsorptionProved : Set
    cubicBoundDoesNotSupplyQuadraticAbsorption :
      scaleFreeCubicByQuadraticAbsorptionProved → Set

canonicalSpectralRigidityAuthorityBoundary :
  SpectralRigidityAuthorityBoundary
canonicalSpectralRigidityAuthorityBoundary =
  spectralRigidityAuthorityBoundary
    ⊤
    ⊥
    (λ impossible → ⊥)
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
