module DASHI.Physics.Closure.NSTriadKNLuoPositiveStrainGradientSignExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUDIT CONTEXT
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- Evan Miller,
-- "A Regularity Criterion for the Navier-Stokes Equation Involving Only
-- the Middle Eigenvalue of the Strain Tensor".
-- Archive for Rational Mechanics and Analysis 235 (2020), 99--139.
-- DOI: 10.1007/s00205-019-01419-z.
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- For an arbitrary exact 3 by 3 gradient matrix G and each column g_k,
--
--   g_k^T G g_k = g_k^T Sym(G) g_k,
--
-- because the antisymmetric contraction vanishes.  Division is avoided by
-- proving twice the raw cubic equals contraction with G + G^T.
--
-- The signed spectral split is then recorded exactly:
--
--   - <S grad u, grad u>
--     = - <S+ grad u, grad u> + <S- grad u, grad u>.
--
-- Thus in the gradient-energy identity the positive spectral part is
-- favourable and the negative spectral part is the potentially amplifying
-- contribution.  This sign is opposite to the interpretation repeatedly
-- used in the NEMGRO manuscript.  The vorticity stretching identity has the
-- opposite signed orientation, and the two are kept type-separated below.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record Matrix3 : Set where
  constructor matrix3
  field
    a11 a12 a13 : ℚ
    a21 a22 a23 : ℚ
    a31 a32 a33 : ℚ

open Matrix3 public

rawQuadratic : Matrix3 → ℚ → ℚ → ℚ → ℚ
rawQuadratic matrix x y z =
  x * (a11 matrix * x + a12 matrix * y + a13 matrix * z)
  + y * (a21 matrix * x + a22 matrix * y + a23 matrix * z)
  + z * (a31 matrix * x + a32 matrix * y + a33 matrix * z)

symmetricNumeratorQuadratic : Matrix3 → ℚ → ℚ → ℚ → ℚ
symmetricNumeratorQuadratic matrix x y z =
  x *
    ( (a11 matrix + a11 matrix) * x
    + (a12 matrix + a21 matrix) * y
    + (a13 matrix + a31 matrix) * z
    )
  + y *
    ( (a21 matrix + a12 matrix) * x
    + (a22 matrix + a22 matrix) * y
    + (a23 matrix + a32 matrix) * z
    )
  + z *
    ( (a31 matrix + a13 matrix) * x
    + (a32 matrix + a23 matrix) * y
    + (a33 matrix + a33 matrix) * z
    )

antisymmetricNumeratorQuadratic : Matrix3 → ℚ → ℚ → ℚ → ℚ
antisymmetricNumeratorQuadratic matrix x y z =
  x *
    ( (a11 matrix - a11 matrix) * x
    + (a12 matrix - a21 matrix) * y
    + (a13 matrix - a31 matrix) * z
    )
  + y *
    ( (a21 matrix - a12 matrix) * x
    + (a22 matrix - a22 matrix) * y
    + (a23 matrix - a32 matrix) * z
    )
  + z *
    ( (a31 matrix - a13 matrix) * x
    + (a32 matrix - a23 matrix) * y
    + (a33 matrix - a33 matrix) * z
    )

twiceRawEqualsSymmetricNumerator :
  ∀ matrix x y z →
  2 * rawQuadratic matrix x y z
  ≡ symmetricNumeratorQuadratic matrix x y z
twiceRawEqualsSymmetricNumerator matrix x y z =
  solve
    ( a11 matrix ∷ a12 matrix ∷ a13 matrix
    ∷ a21 matrix ∷ a22 matrix ∷ a23 matrix
    ∷ a31 matrix ∷ a32 matrix ∷ a33 matrix
    ∷ x ∷ y ∷ z ∷ [])

antisymmetricQuadraticCancels :
  ∀ matrix x y z →
  antisymmetricNumeratorQuadratic matrix x y z ≡ 0ℚ
antisymmetricQuadraticCancels matrix x y z =
  solve
    ( a11 matrix ∷ a12 matrix ∷ a13 matrix
    ∷ a21 matrix ∷ a22 matrix ∷ a23 matrix
    ∷ a31 matrix ∷ a32 matrix ∷ a33 matrix
    ∷ x ∷ y ∷ z ∷ [])

convectiveGradientCubic : Matrix3 → ℚ
convectiveGradientCubic matrix =
  rawQuadratic matrix
    (a11 matrix) (a21 matrix) (a31 matrix)
  + rawQuadratic matrix
    (a12 matrix) (a22 matrix) (a32 matrix)
  + rawQuadratic matrix
    (a13 matrix) (a23 matrix) (a33 matrix)

symmetricGradientCubicNumerator : Matrix3 → ℚ
symmetricGradientCubicNumerator matrix =
  symmetricNumeratorQuadratic matrix
    (a11 matrix) (a21 matrix) (a31 matrix)
  + symmetricNumeratorQuadratic matrix
    (a12 matrix) (a22 matrix) (a32 matrix)
  + symmetricNumeratorQuadratic matrix
    (a13 matrix) (a23 matrix) (a33 matrix)

antisymmetricGradientCubicNumerator : Matrix3 → ℚ
antisymmetricGradientCubicNumerator matrix =
  antisymmetricNumeratorQuadratic matrix
    (a11 matrix) (a21 matrix) (a31 matrix)
  + antisymmetricNumeratorQuadratic matrix
    (a12 matrix) (a22 matrix) (a32 matrix)
  + antisymmetricNumeratorQuadratic matrix
    (a13 matrix) (a23 matrix) (a33 matrix)

integratedPointwiseGradientIdentity :
  ∀ matrix →
  2 * convectiveGradientCubic matrix
  ≡ symmetricGradientCubicNumerator matrix
integratedPointwiseGradientIdentity matrix =
  solve
    ( a11 matrix ∷ a12 matrix ∷ a13 matrix
    ∷ a21 matrix ∷ a22 matrix ∷ a23 matrix
    ∷ a31 matrix ∷ a32 matrix ∷ a33 matrix
    ∷ [])

antisymmetricGradientCubicCancels :
  ∀ matrix →
  antisymmetricGradientCubicNumerator matrix ≡ 0ℚ
antisymmetricGradientCubicCancels matrix =
  solve
    ( a11 matrix ∷ a12 matrix ∷ a13 matrix
    ∷ a21 matrix ∷ a22 matrix ∷ a23 matrix
    ∷ a31 matrix ∷ a32 matrix ∷ a33 matrix
    ∷ [])

record SpectralContractions : Set where
  constructor spectralContractions
  field
    positiveContraction negativeContraction : ℚ
    positiveNonnegative : 0ℚ ≤ positiveContraction
    negativeNonnegative : 0ℚ ≤ negativeContraction

open SpectralContractions public

gradientEnergyNonlinearRHS : SpectralContractions → ℚ
gradientEnergyNonlinearRHS split =
  - positiveContraction split + negativeContraction split

vorticityStretchingRHS : SpectralContractions → ℚ
vorticityStretchingRHS split =
  positiveContraction split - negativeContraction split

gradientSpectralSignIdentity :
  ∀ positive negative →
  - (positive - negative) ≡ - positive + negative
gradientSpectralSignIdentity positive negative =
  solve (positive ∷ negative ∷ [])

vorticitySpectralSignIdentity :
  ∀ positive negative →
  positive - negative ≡ positive + (- negative)
vorticitySpectralSignIdentity positive negative =
  solve (positive ∷ negative ∷ [])

positiveStrainIsFavourableForGradientEnergy :
  ∀ split →
  gradientEnergyNonlinearRHS split ≤ negativeContraction split
positiveStrainIsFavourableForGradientEnergy split =
  let
    base :
      negativeContraction split - positiveContraction split
      ≤ negativeContraction split
    base =
      L2.subtractNonnegativeBelow
        (negativeContraction split)
        (positiveContraction split)
        (positiveNonnegative split)

    rearranged :
      gradientEnergyNonlinearRHS split
      ≡ negativeContraction split - positiveContraction split
    rearranged =
      solve
        ( positiveContraction split
        ∷ negativeContraction split
        ∷ [])
  in
  subst
    (λ left → left ≤ negativeContraction split)
    (sym rearranged)
    base

negativeStrainCanOnlyIncreaseGradientRHS :
  ∀ split →
  - positiveContraction split
  ≤ gradientEnergyNonlinearRHS split
negativeStrainCanOnlyIncreaseGradientRHS split =
  let
    withNegative :
      - positiveContraction split + 0ℚ
      ≤ - positiveContraction split + negativeContraction split
    withNegative =
      ℚₚ.+-monoʳ-≤
        (- positiveContraction split)
        (negativeNonnegative split)

    leftClosed :
      - positiveContraction split + 0ℚ
      ≡ - positiveContraction split
    leftClosed = solve (positiveContraction split ∷ [])
  in
  subst
    (λ left → left ≤ gradientEnergyNonlinearRHS split)
    leftClosed
    withNegative

record GradientVorticitySignBoundary : Set where
  constructor gradientVorticitySignBoundary
  field
    gradientPositiveStrainDestabilising : Set
    vorticityPositiveStrainDestabilising : Set
    signConflationAllowed : Set

canonicalGradientVorticitySignBoundary : GradientVorticitySignBoundary
canonicalGradientVorticitySignBoundary =
  gradientVorticitySignBoundary
    ⊥
    ⊤
    ⊥
  where
  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤)
