module DASHI.Physics.Closure.NSTriadKNAlignedPressureSpectralSurplusRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND78 / ALIGNED PRESSURE SPECTRAL THRESHOLD
--
-- Combine the exact isotropic contraction
--
--   C_I = Omega (Omega-Sigma)/6
--
-- with exact alignment of omega to the smallest deviatoric pressure-Hessian
-- eigenvector
--
--   C_D = lambda3^D Omega.
--
-- Since pressure enters the stretching-acceleration equation with a minus sign,
-- the total pressure contribution factors exactly as
--
--   -(C_I+C_D)
--     = Omega [ -lambda3^D - (Omega-Sigma)/6 ].
--
-- Hence exact aligned pressure is non-enabling whenever
--
--   -lambda3^D <= (Omega-Sigma)/6.
--
-- Including the quadratic self-amplification W.W gives the exact raw inviscid
-- acceleration
--
--   W.W + Omega [ -lambda3^D - (Omega-Sigma)/6 ].
--
-- On a nonpositive pressure bracket this is bounded above by W.W itself.  Thus
-- a Round78 B2 event in that branch cannot get any extra gain from pressure;
-- its quadratic/cross-mode channel must already pay the remaining costs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNIsotropicPressureEnstrophyStrainCriterionRound78Exact as Iso
import DASHI.Physics.Closure.NSTriadKNDeviatoricPressureAlignmentEnableRound78Exact as Dev

alignedPressureContribution : ℚ → ℚ → ℚ → ℚ
alignedPressureContribution enstrophy strainIntensity smallestEigenvalue =
  - Iso.isotropicPressureContraction enstrophy strainIntensity
  - Dev.alignedDeviatoricContraction smallestEigenvalue enstrophy

pressureSpectralBracket : ℚ → ℚ → ℚ → ℚ
pressureSpectralBracket enstrophy strainIntensity smallestEigenvalue =
  (- smallestEigenvalue)
  - Iso.oneSixth * (enstrophy - strainIntensity)

alignedPressureContributionFactors :
  ∀ enstrophy strainIntensity smallestEigenvalue →
  alignedPressureContribution enstrophy strainIntensity smallestEigenvalue
  ≡ enstrophy
      * pressureSpectralBracket enstrophy strainIntensity smallestEigenvalue
alignedPressureContributionFactors enstrophy strainIntensity smallestEigenvalue =
  solve (enstrophy ∷ strainIntensity ∷ smallestEigenvalue ∷ Iso.oneSixth ∷ [])

alignedPressureDepletingWhenBracketNonpositive :
  ∀ enstrophy strainIntensity smallestEigenvalue →
  0ℚ ≤ enstrophy →
  pressureSpectralBracket enstrophy strainIntensity smallestEigenvalue ≤ 0ℚ →
  alignedPressureContribution enstrophy strainIntensity smallestEigenvalue ≤ 0ℚ
alignedPressureDepletingWhenBracketNonpositive
    enstrophy strainIntensity smallestEigenvalue enstrophyNN bracket≤0 =
  let
    instance enstrophyNonnegative = nonNegative enstrophyNN

    product≤zero :
      enstrophy * pressureSpectralBracket enstrophy strainIntensity smallestEigenvalue
      ≤ enstrophy * 0ℚ
    product≤zero =
      ℚP.*-monoˡ-≤-nonNeg enstrophy bracket≤0

    rightZero : enstrophy * 0ℚ ≡ 0ℚ
    rightZero = solve (enstrophy ∷ [])

    factored≤zero :
      enstrophy * pressureSpectralBracket enstrophy strainIntensity smallestEigenvalue
      ≤ 0ℚ
    factored≤zero =
      subst
        (λ right →
          enstrophy
            * pressureSpectralBracket enstrophy strainIntensity smallestEigenvalue
          ≤ right)
        rightZero
        product≤zero
  in
  subst
    (λ left → left ≤ 0ℚ)
    (alignedPressureContributionFactors
      enstrophy strainIntensity smallestEigenvalue)
    factored≤zero

alignedInviscidStretchingAcceleration : ℚ → ℚ → ℚ → ℚ → ℚ
alignedInviscidStretchingAcceleration
    stretchingSquare enstrophy strainIntensity smallestEigenvalue =
  stretchingSquare
  + alignedPressureContribution enstrophy strainIntensity smallestEigenvalue

alignedInviscidStretchingAccelerationFactors :
  ∀ stretchingSquare enstrophy strainIntensity smallestEigenvalue →
  alignedInviscidStretchingAcceleration
    stretchingSquare enstrophy strainIntensity smallestEigenvalue
  ≡ stretchingSquare
      + enstrophy
          * pressureSpectralBracket enstrophy strainIntensity smallestEigenvalue
alignedInviscidStretchingAccelerationFactors
    stretchingSquare enstrophy strainIntensity smallestEigenvalue =
  trans
    (refl)
    (congLeft
      (alignedPressureContributionFactors
        enstrophy strainIntensity smallestEigenvalue))
  where
  congLeft : ∀ {left right : ℚ} → left ≡ right →
    stretchingSquare + left ≡ stretchingSquare + right
  congLeft refl = refl

nonpositivePressureBracketCannotIncreaseQuadraticAcceleration :
  ∀ stretchingSquare enstrophy strainIntensity smallestEigenvalue →
  0ℚ ≤ enstrophy →
  pressureSpectralBracket enstrophy strainIntensity smallestEigenvalue ≤ 0ℚ →
  alignedInviscidStretchingAcceleration
    stretchingSquare enstrophy strainIntensity smallestEigenvalue
  ≤ stretchingSquare
nonpositivePressureBracketCannotIncreaseQuadraticAcceleration
    stretchingSquare enstrophy strainIntensity smallestEigenvalue
    enstrophyNN bracket≤0 =
  let
    pressure≤0 :
      alignedPressureContribution enstrophy strainIntensity smallestEigenvalue ≤ 0ℚ
    pressure≤0 =
      alignedPressureDepletingWhenBracketNonpositive
        enstrophy strainIntensity smallestEigenvalue enstrophyNN bracket≤0

    added :
      stretchingSquare
        + alignedPressureContribution enstrophy strainIntensity smallestEigenvalue
      ≤ stretchingSquare + 0ℚ
    added = ℚP.+-monoˡ-≤ stretchingSquare pressure≤0
  in
  subst
    (λ right →
      alignedInviscidStretchingAcceleration
        stretchingSquare enstrophy strainIntensity smallestEigenvalue
      ≤ right)
    (ℚP.+-identityʳ stretchingSquare)
    added

round78AlignedPressureSpectralFactorizationConstructed : Bool
round78AlignedPressureSpectralFactorizationConstructed = true

round78NonpositivePressureBracketCannotIncreaseQuadraticAcceleration : Bool
round78NonpositivePressureBracketCannotIncreaseQuadraticAcceleration = true

round78PressureEnablingRequiresPositiveSpectralBracket : Bool
round78PressureEnablingRequiresPositiveSpectralBracket = true

round78SelectedCriticalPressureSpectralBracketKnownPositive : Bool
round78SelectedCriticalPressureSpectralBracketKnownPositive = false

round78AlignedPressureSpectralFactorizationConstructedIsTrue :
  round78AlignedPressureSpectralFactorizationConstructed ≡ true
round78AlignedPressureSpectralFactorizationConstructedIsTrue = refl
