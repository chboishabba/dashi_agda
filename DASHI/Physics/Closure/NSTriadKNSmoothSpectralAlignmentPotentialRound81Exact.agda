module DASHI.Physics.Closure.NSTriadKNSmoothSpectralAlignmentPotentialRound81Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Marcus Carlsson,
-- "Lipschitz continuity for isotropic matrix functions",
-- Linear Algebra and its Applications 624 (2021), 259--266.
-- DOI: 10.1016/j.laa.2021.04.006.
--
-- Awad H. Al-Mohy; Nicholas J. Higham,
-- "Computing the Frechet Derivative of the Matrix Exponential, with an
-- Application to Condition Number Estimation",
-- SIAM Journal on Matrix Analysis and Applications 30 (2009), 1639--1657.
-- DOI: 10.1137/080716426.
--
-- Bolin Gao; Lacra Pavel,
-- "On the Properties of the Softmax Function with Application in Game Theory
-- and Reinforcement Learning", arXiv:1704.00805.
-- DOI: 10.48550/arXiv.1704.00805.
--
-- ROUND81 / GAP-FREE BOUNDED SPECTRAL POTENTIAL
--
-- The existing finite-Galerkin audit uses
--
--   P_beta(S) = exp(beta S) / trace(exp(beta S)).
--
-- In an eigenbasis its spectral weights p_i are nonnegative and sum to one,
-- including at repeated eigenvalues.  For a unit vorticity direction, the
-- squared alignment weights alpha_i are likewise nonnegative and sum to one.
-- Therefore
--
--   A = sum_i p_i alpha_i
--
-- is automatically a bounded scalar potential 0 <= A <= 1, with no spectral
-- gap or individual eigenvector derivative in the statement.
--
-- This module proves that simplex algebra exactly.  It does NOT pretend to
-- construct the real matrix exponential in rational arithmetic; the remaining
-- analytic source-facing seam is the actual P_beta Frechet derivative and the
-- signed danger/replenishment inequalities on the selected NS trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

record SpectralProbabilityWeights : Set where
  field
    p1 p2 p3 : ℚ
    p1Nonnegative : 0ℚ ≤ p1
    p2Nonnegative : 0ℚ ≤ p2
    p3Nonnegative : 0ℚ ≤ p3
    sumOne : (p1 + p2) + p3 ≡ 1ℚ

open SpectralProbabilityWeights public

record DirectionAlignmentWeights : Set where
  field
    alpha1 alpha2 alpha3 : ℚ
    alpha1Nonnegative : 0ℚ ≤ alpha1
    alpha2Nonnegative : 0ℚ ≤ alpha2
    alpha3Nonnegative : 0ℚ ≤ alpha3
    sumOne : (alpha1 + alpha2) + alpha3 ≡ 1ℚ

open DirectionAlignmentWeights public

softSpectralAlignmentPotential :
  SpectralProbabilityWeights → DirectionAlignmentWeights → ℚ
softSpectralAlignmentPotential p alpha =
  p1 p * alpha1 alpha
  + p2 p * alpha2 alpha
  + p3 p * alpha3 alpha

probabilityCoordinateBelowOne :
  (p : SpectralProbabilityWeights) →
  (p1 p ≤ 1ℚ) × (p2 p ≤ 1ℚ) × (p3 p ≤ 1ℚ)
probabilityCoordinateBelowOne p = first , second , third
  where
  open import Data.Product using (_×_; _,_)

  p1≤sum : p1 p ≤ (p1 p + p2 p) + p3 p
  p1≤sum =
    let
      p1≤p1p2 : p1 p ≤ p1 p + p2 p
      p1≤p1p2 =
        subst
          (λ left → left ≤ p1 p + p2 p)
          (ℚP.+-identityʳ (p1 p))
          (ℚP.+-mono-≤
            (ℚP.≤-refl {x = p1 p})
            (p2Nonnegative p))
    in
    ℚP.≤-trans p1≤p1p2
      (subst
        (λ left → left ≤ (p1 p + p2 p) + p3 p)
        (ℚP.+-identityʳ (p1 p + p2 p))
        (ℚP.+-mono-≤
          (ℚP.≤-refl {x = p1 p + p2 p})
          (p3Nonnegative p)))

  p2≤p1p2 : p2 p ≤ p1 p + p2 p
  p2≤p1p2 =
    subst
      (λ left → left ≤ p1 p + p2 p)
      (ℚP.+-identityˡ (p2 p))
      (ℚP.+-mono-≤
        (p1Nonnegative p)
        (ℚP.≤-refl {x = p2 p}))

  p2≤sum : p2 p ≤ (p1 p + p2 p) + p3 p
  p2≤sum =
    ℚP.≤-trans p2≤p1p2
      (subst
        (λ left → left ≤ (p1 p + p2 p) + p3 p)
        (ℚP.+-identityʳ (p1 p + p2 p))
        (ℚP.+-mono-≤
          (ℚP.≤-refl {x = p1 p + p2 p})
          (p3Nonnegative p)))

  p3≤sum : p3 p ≤ (p1 p + p2 p) + p3 p
  p3≤sum =
    subst
      (λ left → left ≤ (p1 p + p2 p) + p3 p)
      (ℚP.+-identityˡ (p3 p))
      (ℚP.+-mono-≤
        (let
          zero≤p1p2 : 0ℚ ≤ p1 p + p2 p
          zero≤p1p2 = ℚP.+-mono-≤ (p1Nonnegative p) (p2Nonnegative p)
         in zero≤p1p2)
        (ℚP.≤-refl {x = p3 p}))

  first : p1 p ≤ 1ℚ
  first = subst (p1 p ≤_) (sumOne p) p1≤sum

  second : p2 p ≤ 1ℚ
  second = subst (p2 p ≤_) (sumOne p) p2≤sum

  third : p3 p ≤ 1ℚ
  third = subst (p3 p ≤_) (sumOne p) p3≤sum

softSpectralAlignmentPotentialNonnegative :
  (p : SpectralProbabilityWeights) →
  (alpha : DirectionAlignmentWeights) →
  0ℚ ≤ softSpectralAlignmentPotential p alpha
softSpectralAlignmentPotentialNonnegative p alpha =
  let
    instance
      p1NN : NonNegative (p1 p)
      p1NN = ℚ.nonNegative (p1Nonnegative p)
      p2NN : NonNegative (p2 p)
      p2NN = ℚ.nonNegative (p2Nonnegative p)
      p3NN : NonNegative (p3 p)
      p3NN = ℚ.nonNegative (p3Nonnegative p)
      a1NN : NonNegative (alpha1 alpha)
      a1NN = ℚ.nonNegative (alpha1Nonnegative alpha)
      a2NN : NonNegative (alpha2 alpha)
      a2NN = ℚ.nonNegative (alpha2Nonnegative alpha)
      a3NN : NonNegative (alpha3 alpha)
      a3NN = ℚ.nonNegative (alpha3Nonnegative alpha)

    firstNN = ℚP.nonNegative⁻¹ (p1 p * alpha1 alpha)
    secondNN = ℚP.nonNegative⁻¹ (p2 p * alpha2 alpha)
    thirdNN = ℚP.nonNegative⁻¹ (p3 p * alpha3 alpha)
  in
  ℚP.+-mono-≤ (ℚP.+-mono-≤ firstNN secondNN) thirdNN

softSpectralAlignmentPotentialBelowOne :
  (p : SpectralProbabilityWeights) →
  (alpha : DirectionAlignmentWeights) →
  softSpectralAlignmentPotential p alpha ≤ 1ℚ
softSpectralAlignmentPotentialBelowOne p alpha =
  let
    bounds = probabilityCoordinateBelowOne p
    open import Data.Product using (proj₁; proj₂)
    p1≤1 = proj₁ bounds
    p2≤1 = proj₁ (proj₂ bounds)
    p3≤1 = proj₂ (proj₂ bounds)

    instance
      a1NN : NonNegative (alpha1 alpha)
      a1NN = ℚ.nonNegative (alpha1Nonnegative alpha)
      a2NN : NonNegative (alpha2 alpha)
      a2NN = ℚ.nonNegative (alpha2Nonnegative alpha)
      a3NN : NonNegative (alpha3 alpha)
      a3NN = ℚ.nonNegative (alpha3Nonnegative alpha)

    first : p1 p * alpha1 alpha ≤ 1ℚ * alpha1 alpha
    first = ℚP.*-monoʳ-≤-nonNeg (alpha1 alpha) p1≤1
    second : p2 p * alpha2 alpha ≤ 1ℚ * alpha2 alpha
    second = ℚP.*-monoʳ-≤-nonNeg (alpha2 alpha) p2≤1
    third : p3 p * alpha3 alpha ≤ 1ℚ * alpha3 alpha
    third = ℚP.*-monoʳ-≤-nonNeg (alpha3 alpha) p3≤1

    summed = ℚP.+-mono-≤ (ℚP.+-mono-≤ first second) third

    upperIsOne :
      1ℚ * alpha1 alpha + 1ℚ * alpha2 alpha + 1ℚ * alpha3 alpha ≡ 1ℚ
    upperIsOne =
      trans
        (cong₂ _+_
          (cong₂ _+_ (ℚP.*-identityˡ (alpha1 alpha)) (ℚP.*-identityˡ (alpha2 alpha)))
          (ℚP.*-identityˡ (alpha3 alpha)))
        (sumOne alpha)
      where
      open import Relation.Binary.PropositionalEquality using (cong₂)
  in
  subst
    (λ upper → softSpectralAlignmentPotential p alpha ≤ upper)
    upperIsOne
    summed

round81SmoothSpectralAlignmentPotentialNeedsSpectralGap : Bool
round81SmoothSpectralAlignmentPotentialNeedsSpectralGap = false

round81SmoothSpectralAlignmentPotentialBoundedZeroOne : Bool
round81SmoothSpectralAlignmentPotentialBoundedZeroOne = true

round81SmoothSpectralAlignmentPotentialBoundedZeroOneIsTrue :
  round81SmoothSpectralAlignmentPotentialBoundedZeroOne ≡ true
round81SmoothSpectralAlignmentPotentialBoundedZeroOneIsTrue = refl
