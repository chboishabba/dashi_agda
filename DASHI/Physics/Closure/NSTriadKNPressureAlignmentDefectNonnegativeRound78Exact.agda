module DASHI.Physics.Closure.NSTriadKNPressureAlignmentDefectNonnegativeRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND78 / EXACT-ALIGNMENT IS THE MAXIMAL ENABLING ENDPOINT
--
-- For ordered deviatoric pressure eigenvalues
--
--   lambda1 >= lambda2 >= lambda3
--
-- and genuine squared alignment weights alpha_i>=0, Round78's defect
--
--   D_align
--     = (lambda1-lambda3) alpha1
--       + (lambda2-lambda3) alpha2
--
-- is nonnegative.  Hence
--
--   -lambda3 - D_align <= -lambda3.
--
-- Exact alignment with the smallest pressure-Hessian eigenvector therefore
-- maximizes the deviatoric enabling contribution for a fixed spectrum and
-- enstrophy.  Imperfect alignment can only reduce the pressure spectral bracket.
-- This is an exact pointwise spectral theorem; no DNS alignment statistics are
-- needed for the inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNDeviatoricPressureAlignmentDefectRound78Exact as Defect
import DASHI.Physics.Closure.NSTriadKNIsotropicPressureEnstrophyStrainCriterionRound78Exact as Iso
import DASHI.Physics.Closure.NSTriadKNPressureAlignmentDefectSpectralBracketRound78Exact as Spectral
import DASHI.Physics.Closure.NSTriadKNAlignedPressureSpectralSurplusRound78Exact as Aligned

record OrderedNonnegativePressureAlignment
    (alignment : Defect.PressureEigenframeAlignment) : Set where
  field
    lambda2BelowLambda1 : Defect.lambda2 alignment ≤ Defect.lambda1 alignment
    lambda3BelowLambda2 : Defect.lambda3 alignment ≤ Defect.lambda2 alignment
    alpha1Nonnegative : 0ℚ ≤ Defect.alpha1 alignment
    alpha2Nonnegative : 0ℚ ≤ Defect.alpha2 alignment
    alpha3Nonnegative : 0ℚ ≤ Defect.alpha3 alignment

open OrderedNonnegativePressureAlignment public

gapNonnegative : ∀ {lower upper : ℚ} → lower ≤ upper → 0ℚ ≤ upper - lower
gapNonnegative = Iso.differenceNonnegative

alignmentDefectNonnegative :
  ∀ {alignment} →
  OrderedNonnegativePressureAlignment alignment →
  0ℚ ≤ Defect.alignmentDefectCost alignment
alignmentDefectNonnegative {alignment} ordered =
  let
    l3BelowL1 : Defect.lambda3 alignment ≤ Defect.lambda1 alignment
    l3BelowL1 =
      ℚP.≤-trans
        (lambda3BelowLambda2 ordered)
        (lambda2BelowLambda1 ordered)

    gap1NN : 0ℚ ≤ Defect.lambda1 alignment - Defect.lambda3 alignment
    gap1NN = gapNonnegative l3BelowL1

    gap2NN : 0ℚ ≤ Defect.lambda2 alignment - Defect.lambda3 alignment
    gap2NN = gapNonnegative (lambda3BelowLambda2 ordered)

    firstNN :
      0ℚ ≤
        (Defect.lambda1 alignment - Defect.lambda3 alignment)
        * Defect.alpha1 alignment
    firstNN = ℚP.0≤*0≤ gap1NN (alpha1Nonnegative ordered)

    secondNN :
      0ℚ ≤
        (Defect.lambda2 alignment - Defect.lambda3 alignment)
        * Defect.alpha2 alignment
    secondNN = ℚP.0≤*0≤ gap2NN (alpha2Nonnegative ordered)
  in
  ℚP.+-mono-≤ firstNN secondNN

imperfectAlignmentDeviatoricEnableBelowExactAlignment :
  ∀ {alignment} →
  OrderedNonnegativePressureAlignment alignment →
  (- Defect.lambda3 alignment) - Defect.alignmentDefectCost alignment
  ≤ - Defect.lambda3 alignment
imperfectAlignmentDeviatoricEnableBelowExactAlignment {alignment} ordered =
  let
    defectNN = alignmentDefectNonnegative ordered
    negDefect≤0 = ℚP.neg-antimono-≤ defectNN
    shifted = ℚP.+-monoˡ-≤ (- Defect.lambda3 alignment) negDefect≤0
  in
  shifted

pressureBracketWithDefectBelowExactAlignedBracket :
  ∀ enstrophy strainIntensity {alignment} →
  OrderedNonnegativePressureAlignment alignment →
  Spectral.pressureBracketWithAlignmentDefect
      enstrophy strainIntensity alignment
  ≤ Aligned.pressureSpectralBracket
      enstrophy strainIntensity (Defect.lambda3 alignment)
pressureBracketWithDefectBelowExactAlignedBracket
    enstrophy strainIntensity {alignment} ordered =
  let
    enableBound = imperfectAlignmentDeviatoricEnableBelowExactAlignment ordered
  in
  ℚP.+-monoʳ-≤
    (- Iso.oneSixth * (enstrophy - strainIntensity))
    enableBound

round78AlignmentDefectNonnegativeForOrderedSpectrum : Bool
round78AlignmentDefectNonnegativeForOrderedSpectrum = true

round78ExactSmallestEigenvectorAlignmentMaximizesPressureEnable : Bool
round78ExactSmallestEigenvectorAlignmentMaximizesPressureEnable = true

round78ExactSmallestEigenvectorAlignmentMaximizesPressureEnableIsTrue :
  round78ExactSmallestEigenvectorAlignmentMaximizesPressureEnable ≡ true
round78ExactSmallestEigenvectorAlignmentMaximizesPressureEnableIsTrue = refl
