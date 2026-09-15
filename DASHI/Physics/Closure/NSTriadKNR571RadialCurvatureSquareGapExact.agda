module DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureSquareGapExact where

------------------------------------------------------------------------
-- R571 GATE-A / A2 CENTERED RADIAL DEFECT -> SQUARE-GAP NUMERATORS
--
-- The preferred R571 Taylor choice leaves one centered radial defect
--
--   D = (rMinus - r0) + (rPlus - r0).
--
-- This owner performs only the exact denominator-cleared algebra needed to
-- expose the older square-gap geometry.  For rational radii,
--
--   D (rMinus+r0) (rPlus+r0)
--     = (rMinus^2-r0^2)(rPlus+r0)
--       + (rPlus^2-r0^2)(rMinus+r0).
--
-- Thus A2 no longer needs to be treated as an opaque Taylor remainder: its
-- numerator is built from the same difference-times-sum square-gap algebra
-- already isolated in Round127.  What is NOT proved here is the ordered-real
-- lower bound/cancellation for the two positive radial sums, nor the geometric
-- estimate converting the resulting square-gap combination into a uniform
-- |y|^2 A2 bound.  Those remain the analytic payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNExternalHHSameHelicityGapProductRound127Exact as R127

centeredRadiusDefect : ℚ → ℚ → ℚ → ℚ
centeredRadiusDefect rMinus r0 rPlus =
  (rMinus - r0) + (rPlus - r0)

radialSum : ℚ → ℚ → ℚ
radialSum r r0 = r + r0

squareGap : ℚ → ℚ → ℚ
squareGap r r0 = r * r - r0 * r0

minusIncrementTimesRadialSumIsSquareGap :
  (rMinus r0 : ℚ) →
  (rMinus - r0) * radialSum rMinus r0
  ≡ squareGap rMinus r0
minusIncrementTimesRadialSumIsSquareGap rMinus r0 =
  solve (rMinus ∷ r0 ∷ [])

plusIncrementTimesRadialSumIsSquareGap :
  (rPlus r0 : ℚ) →
  (rPlus - r0) * radialSum rPlus r0
  ≡ squareGap rPlus r0
plusIncrementTimesRadialSumIsSquareGap rPlus r0 =
  solve (rPlus ∷ r0 ∷ [])

centeredRadiusDefectClearedByRadialSums :
  (rMinus r0 rPlus : ℚ) →
  centeredRadiusDefect rMinus r0 rPlus
    * radialSum rMinus r0
    * radialSum rPlus r0
  ≡
  squareGap rMinus r0 * radialSum rPlus r0
    + squareGap rPlus r0 * radialSum rMinus r0
centeredRadiusDefectClearedByRadialSums rMinus r0 rPlus =
  solve (rMinus ∷ r0 ∷ rPlus ∷ [])

-- Round127 is the theorem-bearing historical owner for precisely the
-- difference-times-radial-sum = square-gap factorization used above.  This
-- tranche changes the coordinate (center/minus/plus) but not the mathematics.
r571A2R127SquareGapAlgebraReused : Bool
r571A2R127SquareGapAlgebraReused =
  R127.round127SameHelicityGapProductFactorizationClosed

r571A2CenteredRadiusDefectSquareGapRationalized : Bool
r571A2CenteredRadiusDefectSquareGapRationalized = true

r571A2IntroducesNewTaylorFramework : Bool
r571A2IntroducesNewTaylorFramework = false

r571A2OrderedRadialDenominatorPaymentClosed : Bool
r571A2OrderedRadialDenominatorPaymentClosed = false

r571A2SquareGapGeometryToUniformCurvatureClosed : Bool
r571A2SquareGapGeometryToUniformCurvatureClosed = false

r571A2UniformCurvatureEstimateClosed : Bool
r571A2UniformCurvatureEstimateClosed = false

r571A2ClosesR568 : Bool
r571A2ClosesR568 = false

r571A2CenteredRadiusDefectSquareGapRationalizedIsTrue :
  r571A2CenteredRadiusDefectSquareGapRationalized ≡ true
r571A2CenteredRadiusDefectSquareGapRationalizedIsTrue = refl

r571A2OrderedRadialDenominatorPaymentClosedIsFalse :
  r571A2OrderedRadialDenominatorPaymentClosed ≡ false
r571A2OrderedRadialDenominatorPaymentClosedIsFalse = refl
