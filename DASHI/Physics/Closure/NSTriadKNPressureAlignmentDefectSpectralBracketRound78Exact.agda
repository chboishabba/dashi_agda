module DASHI.Physics.Closure.NSTriadKNPressureAlignmentDefectSpectralBracketRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND78 / IMPERFECT-ALIGNMENT PRESSURE BRACKET
--
-- Combine the exact pressure-eigenframe alignment defect with the exact local
-- isotropic pressure formula.  For enstrophy Omega and strain intensity Sigma,
--
--   - omega^T H omega
--     = Omega [
--         -lambda3^D
--         - D_align
--         - (Omega-Sigma)/6
--       ],
--
-- where
--
--   D_align
--     = (lambda1^D-lambda3^D) alpha1
--       + (lambda2^D-lambda3^D) alpha2.
--
-- This is the exact scalar pressure currency for the existing packet-coherence
-- coordinates alpha_i.  A nonpositive bracket means pressure cannot increase
-- the quadratic stretching acceleration.  A positive bracket is necessary if
-- pressure itself is to provide an enabling contribution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNIsotropicPressureEnstrophyStrainCriterionRound78Exact as Iso
import DASHI.Physics.Closure.NSTriadKNDeviatoricPressureAlignmentDefectRound78Exact as Defect

pressureBracketWithAlignmentDefect :
  ℚ → ℚ → Defect.PressureEigenframeAlignment → ℚ
pressureBracketWithAlignmentDefect enstrophy strainIntensity alignment =
  (- Defect.lambda3 alignment)
  - Defect.alignmentDefectCost alignment
  - Iso.oneSixth * (enstrophy - strainIntensity)

pressureContributionWithAlignmentDefect :
  ℚ → ℚ → Defect.PressureEigenframeAlignment → ℚ
pressureContributionWithAlignmentDefect enstrophy strainIntensity alignment =
  - Iso.isotropicPressureContraction enstrophy strainIntensity
  - Defect.fullDeviatoricContraction enstrophy alignment

pressureContributionWithAlignmentDefectFactors :
  ∀ enstrophy strainIntensity alignment →
  pressureContributionWithAlignmentDefect enstrophy strainIntensity alignment
  ≡ enstrophy
      * pressureBracketWithAlignmentDefect enstrophy strainIntensity alignment
pressureContributionWithAlignmentDefectFactors enstrophy strainIntensity alignment =
  trans
    (cong
      (λ negatedDeviatoric →
        - Iso.isotropicPressureContraction enstrophy strainIntensity
        + negatedDeviatoric)
      (Defect.negatedFullDeviatoricContractionFactors enstrophy alignment))
    (solve
      ( enstrophy
      ∷ strainIntensity
      ∷ Defect.lambda3 alignment
      ∷ Defect.alignmentDefectCost alignment
      ∷ Iso.oneSixth
      ∷ []))

pressureContributionNonpositiveWhenDefectBracketNonpositive :
  ∀ enstrophy strainIntensity alignment →
  0ℚ ≤ enstrophy →
  pressureBracketWithAlignmentDefect enstrophy strainIntensity alignment ≤ 0ℚ →
  pressureContributionWithAlignmentDefect enstrophy strainIntensity alignment ≤ 0ℚ
pressureContributionNonpositiveWhenDefectBracketNonpositive
    enstrophy strainIntensity alignment enstrophyNN bracket≤0 =
  let
    instance enstrophyNonnegative = nonNegative enstrophyNN

    product≤zero :
      enstrophy
        * pressureBracketWithAlignmentDefect enstrophy strainIntensity alignment
      ≤ enstrophy * 0ℚ
    product≤zero = ℚP.*-monoˡ-≤-nonNeg enstrophy bracket≤0

    rightZero : enstrophy * 0ℚ ≡ 0ℚ
    rightZero = solve (enstrophy ∷ [])

    factored≤zero :
      enstrophy
        * pressureBracketWithAlignmentDefect enstrophy strainIntensity alignment
      ≤ 0ℚ
    factored≤zero =
      subst
        (λ right →
          enstrophy
            * pressureBracketWithAlignmentDefect enstrophy strainIntensity alignment
          ≤ right)
        rightZero
        product≤zero
  in
  subst
    (λ left → left ≤ 0ℚ)
    (pressureContributionWithAlignmentDefectFactors
      enstrophy strainIntensity alignment)
    factored≤zero

inviscidAccelerationWithAlignmentDefect :
  ℚ → ℚ → ℚ → Defect.PressureEigenframeAlignment → ℚ
inviscidAccelerationWithAlignmentDefect
    stretchingSquare enstrophy strainIntensity alignment =
  stretchingSquare
  + pressureContributionWithAlignmentDefect enstrophy strainIntensity alignment

nonpositiveDefectBracketCannotIncreaseQuadraticAcceleration :
  ∀ stretchingSquare enstrophy strainIntensity alignment →
  0ℚ ≤ enstrophy →
  pressureBracketWithAlignmentDefect enstrophy strainIntensity alignment ≤ 0ℚ →
  inviscidAccelerationWithAlignmentDefect
    stretchingSquare enstrophy strainIntensity alignment
  ≤ stretchingSquare
nonpositiveDefectBracketCannotIncreaseQuadraticAcceleration
    stretchingSquare enstrophy strainIntensity alignment enstrophyNN bracket≤0 =
  let
    pressure≤0 =
      pressureContributionNonpositiveWhenDefectBracketNonpositive
        enstrophy strainIntensity alignment enstrophyNN bracket≤0
    added = ℚP.+-monoˡ-≤ stretchingSquare pressure≤0
  in
  subst
    (λ right →
      inviscidAccelerationWithAlignmentDefect
        stretchingSquare enstrophy strainIntensity alignment
      ≤ right)
    (ℚP.+-identityʳ stretchingSquare)
    added

round78PressureAlignmentDefectSpectralBracketConstructed : Bool
round78PressureAlignmentDefectSpectralBracketConstructed = true

round78NonpositiveDefectBracketCannotIncreaseQuadraticAcceleration : Bool
round78NonpositiveDefectBracketCannotIncreaseQuadraticAcceleration = true

round78SelectedCriticalDefectBracketKnownPositive : Bool
round78SelectedCriticalDefectBracketKnownPositive = false

round78PressureAlignmentDefectSpectralBracketConstructedIsTrue :
  round78PressureAlignmentDefectSpectralBracketConstructed ≡ true
round78PressureAlignmentDefectSpectralBracketConstructedIsTrue = refl
