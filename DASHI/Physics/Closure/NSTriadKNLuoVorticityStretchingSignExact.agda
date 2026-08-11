module DASHI.Physics.Closure.NSTriadKNLuoVorticityStretchingSignExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Peter Constantin and Charles Fefferman,
-- "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Evan Miller,
-- "A Regularity Criterion for the Navier-Stokes Equation Involving Only
-- the Middle Eigenvalue of the Strain Tensor".
-- Archive for Rational Mechanics and Analysis 235 (2020), 99--139.
-- DOI: 10.1007/s00205-019-01419-z.
--
-- DASHI CONTRIBUTION
--
-- For every vorticity vector omega and exact gradient matrix G,
--
--   omega^T G omega = omega^T Sym(G) omega,
--
-- and the antisymmetric contribution vanishes.  This reuses the checked
-- column-quadratic identity without conflating the enstrophy and differentiated
-- velocity-gradient balances.
--
-- If S = S+ - S-, then the vorticity-stretching orientation is
--
--   <omega,S omega> = <omega,S+ omega> - <omega,S- omega>.
--
-- Thus positive strain is potentially amplifying for enstrophy while negative
-- strain is favourable.  This is the reverse of the sign in the gradient
-- energy RHS `-<S grad u,grad u>`.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPositiveStrainGradientSignExact as Sign
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

vorticityGradientContraction : Sign.Matrix3 → Gram.Vec3 → ℚ
vorticityGradientContraction matrix omega =
  Sign.rawQuadratic matrix
    (Gram.x omega) (Gram.y omega) (Gram.z omega)

vorticitySymmetricNumeratorContraction :
  Sign.Matrix3 → Gram.Vec3 → ℚ
vorticitySymmetricNumeratorContraction matrix omega =
  Sign.symmetricNumeratorQuadratic matrix
    (Gram.x omega) (Gram.y omega) (Gram.z omega)

vorticityAntisymmetricNumeratorContraction :
  Sign.Matrix3 → Gram.Vec3 → ℚ
vorticityAntisymmetricNumeratorContraction matrix omega =
  Sign.antisymmetricNumeratorQuadratic matrix
    (Gram.x omega) (Gram.y omega) (Gram.z omega)

twiceVorticityGradientEqualsSymmetricNumerator :
  ∀ matrix omega →
  2 * vorticityGradientContraction matrix omega
  ≡ vorticitySymmetricNumeratorContraction matrix omega
twiceVorticityGradientEqualsSymmetricNumerator matrix omega =
  Sign.twiceRawEqualsSymmetricNumerator
    matrix (Gram.x omega) (Gram.y omega) (Gram.z omega)

vorticityAntisymmetricContractionCancels :
  ∀ matrix omega →
  vorticityAntisymmetricNumeratorContraction matrix omega ≡ 0ℚ
vorticityAntisymmetricContractionCancels matrix omega =
  Sign.antisymmetricQuadraticCancels
    matrix (Gram.x omega) (Gram.y omega) (Gram.z omega)

record VorticitySpectralContractions : Set where
  constructor vorticitySpectralContractions
  field
    positiveStretch negativeStretch : ℚ
    positiveStretchNonnegative : 0ℚ ≤ positiveStretch
    negativeStretchNonnegative : 0ℚ ≤ negativeStretch

open VorticitySpectralContractions public

vorticityStretching : VorticitySpectralContractions → ℚ
vorticityStretching split =
  positiveStretch split - negativeStretch split

vorticitySpectralSplitIdentity :
  ∀ positive negative →
  positive - negative ≡ positive + (- negative)
vorticitySpectralSplitIdentity positive negative =
  solve (positive ∷ negative ∷ [])

negativeStrainIsFavourableForEnstrophy :
  ∀ split →
  vorticityStretching split ≤ positiveStretch split
negativeStrainIsFavourableForEnstrophy split =
  L2.subtractNonnegativeBelow
    (positiveStretch split)
    (negativeStretch split)
    (negativeStretchNonnegative split)

positiveStrainCanOnlyIncreaseEnstrophyRHS :
  ∀ split →
  - negativeStretch split ≤ vorticityStretching split
positiveStrainCanOnlyIncreaseEnstrophyRHS split =
  let
    shifted :
      0ℚ + (- negativeStretch split)
      ≤ positiveStretch split + (- negativeStretch split)
    shifted =
      ℚₚ.+-monoʳ-≤
        (- negativeStretch split)
        (positiveStretchNonnegative split)

    leftClosed :
      0ℚ + (- negativeStretch split)
      ≡ - negativeStretch split
    leftClosed = solve (negativeStretch split ∷ [])

    rightClosed :
      positiveStretch split + (- negativeStretch split)
      ≡ vorticityStretching split
    rightClosed = solve
      (positiveStretch split ∷ negativeStretch split ∷ [])

    normalizedLeft :
      - negativeStretch split
      ≤ positiveStretch split + (- negativeStretch split)
    normalizedLeft =
      subst
        (λ left →
          left ≤ positiveStretch split + (- negativeStretch split))
        leftClosed
        shifted
  in
  subst
    (λ right → - negativeStretch split ≤ right)
    rightClosed
    normalizedLeft

record GradientEnstrophySignSeparation : Set where
  constructor gradientEnstrophySignSeparation
  field
    positiveStrainFavourableInGradientBalance : Set
    positiveStrainPotentiallyAmplifyingInEnstrophyBalance : Set
    balancesMayBeSignConflated : Set

canonicalGradientEnstrophySignSeparation :
  GradientEnstrophySignSeparation
canonicalGradientEnstrophySignSeparation =
  gradientEnstrophySignSeparation ⊤ ⊤ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
