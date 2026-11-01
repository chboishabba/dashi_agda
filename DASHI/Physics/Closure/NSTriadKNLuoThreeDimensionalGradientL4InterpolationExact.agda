module DASHI.Physics.Closure.NSTriadKNLuoThreeDimensionalGradientL4InterpolationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUDIT CONTEXT
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Charles R. Doering and J. D. Gibbon,
-- "Applied Analysis of the Navier-Stokes Equations".
-- DOI: 10.1017/CBO9780511608803.
--
-- DASHI CONTRIBUTION
--
-- The three-dimensional Gagliardo--Nirenberg exponent pattern is recorded
-- exactly:
--
--   ||grad u||_4
--     <= C ||grad u||_2^(1/4) ||grad^2 u||_2^(3/4),
--
-- hence after squaring the exponents are 1/2 and 3/2, not 1 and 1.
--
-- The radical-free Young step is proved from the exact polynomial identity
--
--   3 x^4 + y^4 - 4 x^3 y
--     = (x-y)^2 ((x+y)^2 + 2 x^2) >= 0.
--
-- Under x^4 = ||Delta u||_2^2 and y^4 = ||grad u||_2^6 this produces the
-- classical sixth-power gradient remainder.  It cannot yield unconditional
-- linear absorption by Laplacian dissipation alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as Nat
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record QuarterExponentPair : Set where
  constructor quarterExponentPair
  field
    lowNumerator highNumerator denominator : ℕ

open QuarterExponentPair public

threeDimensionalL4Exponents : QuarterExponentPair
threeDimensionalL4Exponents = quarterExponentPair 1 3 4

manuscriptDisplayedExponents : QuarterExponentPair
manuscriptDisplayedExponents = quarterExponentPair 1 1 1

correctLowPlusHighNumerator :
  Nat._+_
    (lowNumerator threeDimensionalL4Exponents)
    (highNumerator threeDimensionalL4Exponents)
  ≡ denominator threeDimensionalL4Exponents
correctLowPlusHighNumerator = refl

square : ℚ → ℚ
square = L2.square

fourth : ℚ → ℚ
fourth value = square value * square value

cubicYoungMonomial : ℚ → ℚ → ℚ
cubicYoungMonomial x y = x * x * x * y

youngDefect : ℚ → ℚ → ℚ
youngDefect x y =
  square (x - y)
  * (square (x + y) + square x + square x)

youngDefectIdentity :
  ∀ x y →
  3 * fourth x + fourth y
  ≡ 4 * cubicYoungMonomial x y + youngDefect x y
youngDefectIdentity x y = solve (x ∷ y ∷ [])

doubledSquareNonnegative :
  ∀ value → 0ℚ ≤ square value + square value
doubledSquareNonnegative value =
  L2.addNonnegative
    (L2.squareNonnegative value)
    (L2.squareNonnegative value)

secondYoungFactorNonnegative :
  ∀ x y →
  0ℚ ≤ square (x + y) + square x + square x
secondYoungFactorNonnegative x y =
  L2.addNonnegative
    (L2.squareNonnegative (x + y))
    (doubledSquareNonnegative x)

youngDefectNonnegative :
  ∀ x y → 0ℚ ≤ youngDefect x y
youngDefectNonnegative x y =
  let
    instance
      firstNN = nonNegative (L2.squareNonnegative (x - y))
      secondNN = nonNegative (secondYoungFactorNonnegative x y)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (square (x - y))
          (square (x + y) + square x + square x)
  in
  ℚₚ.nonNegative⁻¹ (youngDefect x y)

quarticYoungInequality :
  ∀ x y →
  4 * cubicYoungMonomial x y
  ≤ 3 * fourth x + fourth y
quarticYoungInequality x y =
  let
    nonlinear = 4 * cubicYoungMonomial x y
    defect = youngDefect x y

    addDefect : nonlinear ≤ nonlinear + defect
    addDefect =
      subst
        (λ lower → lower ≤ nonlinear + defect)
        (ℚₚ.+-identityʳ nonlinear)
        (ℚₚ.+-monoʳ-≤ nonlinear (youngDefectNonnegative x y))
  in
  subst
    (λ upper → nonlinear ≤ upper)
    (sym (youngDefectIdentity x y))
    addDefect

record GradientInterpolationPowerModel : Set where
  constructor gradientInterpolationPowerModel
  field
    laplacianQuarterRoot gradientThreeHalfRoot : ℚ
    laplacianSquared gradientSixth nonlinearProduct : ℚ

    laplacianFourthMeaning :
      fourth laplacianQuarterRoot ≡ laplacianSquared

    gradientFourthMeaning :
      fourth gradientThreeHalfRoot ≡ gradientSixth

    nonlinearMeaning :
      cubicYoungMonomial
        laplacianQuarterRoot gradientThreeHalfRoot
      ≡ nonlinearProduct

open GradientInterpolationPowerModel public

threeDimensionalYoungClosure :
  ∀ model →
  4 * nonlinearProduct model
  ≤ 3 * laplacianSquared model + gradientSixth model
threeDimensionalYoungClosure model =
  let
    base =
      quarticYoungInequality
        (laplacianQuarterRoot model)
        (gradientThreeHalfRoot model)

    leftMeaning :
      4 * cubicYoungMonomial
        (laplacianQuarterRoot model)
        (gradientThreeHalfRoot model)
      ≡ 4 * nonlinearProduct model
    leftMeaning =
      cong (λ value → 4 * value) (nonlinearMeaning model)

    rightMeaning :
      3 * fourth (laplacianQuarterRoot model)
        + fourth (gradientThreeHalfRoot model)
      ≡ 3 * laplacianSquared model + gradientSixth model
    rightMeaning
      rewrite laplacianFourthMeaning model
            | gradientFourthMeaning model = refl

    normalizedLeft :
      4 * nonlinearProduct model
      ≤
      3 * fourth (laplacianQuarterRoot model)
        + fourth (gradientThreeHalfRoot model)
    normalizedLeft =
      subst
        (λ left →
          left
          ≤ 3 * fourth (laplacianQuarterRoot model)
            + fourth (gradientThreeHalfRoot model))
        leftMeaning
        base
  in
  subst
    (λ right → 4 * nonlinearProduct model ≤ right)
    rightMeaning
    normalizedLeft

record InterpolationAuthorityBoundary : Set where
  constructor interpolationAuthorityBoundary
  field
    correctThreeDimensionalExponentPatternRecorded : Set
    radicalFreeYoungStepProved : Set
    sixthPowerGradientRemainderPresent : Set
    unconditionalLinearAbsorptionObtained : Set

canonicalInterpolationAuthorityBoundary : InterpolationAuthorityBoundary
canonicalInterpolationAuthorityBoundary =
  interpolationAuthorityBoundary ⊤ ⊤ ⊤ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
