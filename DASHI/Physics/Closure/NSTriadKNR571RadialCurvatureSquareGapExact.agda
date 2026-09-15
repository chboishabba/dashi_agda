module DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureSquareGapExact where

------------------------------------------------------------------------
-- R571 GATE-A / A2 CENTERED RADIAL DEFECT -> SQUARE-GAP NUMERATORS
--
-- The preferred R571 Taylor choice leaves one centered radial defect
--
--   D = (rMinus - r0) + (rPlus - r0).
--
-- This owner performs only exact denominator-cleared algebra.  First,
--
--   D (rMinus+r0) (rPlus+r0)
--     = (rMinus^2-r0^2)(rPlus+r0)
--       + (rPlus^2-r0^2)(rMinus+r0).
--
-- Second, the same defect may be viewed as a triangle excess.  Whenever
--
--   rK^2 = rP^2 + rQ^2 + 2 c,
--
-- exact polarization gives
--
--   (rP+rQ-rK)(rP+rQ+rK) = 2 (rP rQ - c).
--
-- For centered shifts p=k+y and q=k-y, the intended same-object specialization
-- has output p+q=2k and hence rK=2 r0.  That carrier identification and the
-- quantitative angular/radial denominator estimate remain outside this owner.
--
-- Thus A2 is no longer an opaque Taylor remainder: its numerator is exposed in
-- the same square-gap/polarization language already used by the historical NS
-- geometry.  No uniform |y|^2 A2 estimate is claimed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNExternalHHSameHelicityGapProductRound127Exact as R127

centeredRadiusDefect : ℚ → ℚ → ℚ → ℚ
centeredRadiusDefect rMinus r0 rPlus =
  (rMinus - r0) + (rPlus - r0)

radialSum : ℚ → ℚ → ℚ
radialSum r r0 = r + r0

squareGap : ℚ → ℚ → ℚ
squareGap r r0 = r * r - r0 * r0

two : ℚ
two = 1ℚ + 1ℚ

triangleExcess : ℚ → ℚ → ℚ → ℚ
triangleExcess rP rQ rK = (rP + rQ) - rK

triangleSum : ℚ → ℚ → ℚ → ℚ
triangleSum rP rQ rK = (rP + rQ) + rK

angularDefectNumerator : ℚ → ℚ → ℚ → ℚ
angularDefectNumerator rP rQ cross = two * (rP * rQ - cross)

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

triangleExcessProductExpanded :
  (rP rQ rK : ℚ) →
  triangleExcess rP rQ rK * triangleSum rP rQ rK
  ≡ rP * rP + rQ * rQ + two * (rP * rQ) - rK * rK
triangleExcessProductExpanded rP rQ rK =
  solve (rP ∷ rQ ∷ rK ∷ [])

triangleExcessTimesSumIsAngularDefectNumerator :
  (rP rQ rK cross : ℚ) →
  rK * rK ≡ rP * rP + rQ * rQ + two * cross →
  triangleExcess rP rQ rK * triangleSum rP rQ rK
  ≡ angularDefectNumerator rP rQ cross
triangleExcessTimesSumIsAngularDefectNumerator rP rQ rK cross outputSquare =
  trans
    (triangleExcessProductExpanded rP rQ rK)
    (trans
      (cong
        (λ output2 →
          rP * rP + rQ * rQ + two * (rP * rQ) - output2)
        outputSquare)
      (solve (rP ∷ rQ ∷ cross ∷ [])))

-- Round127 is the theorem-bearing historical owner for precisely the
-- difference-times-radial-sum = square-gap factorization used above.  This
-- tranche changes the coordinate (center/minus/plus) but not that mathematics.
r571A2R127SquareGapAlgebraReused : Bool
r571A2R127SquareGapAlgebraReused =
  R127.round127SameHelicityGapProductFactorizationClosed

r571A2CenteredRadiusDefectSquareGapRationalized : Bool
r571A2CenteredRadiusDefectSquareGapRationalized = true

r571A2TriangleExcessPolarizationFactorizationClosed : Bool
r571A2TriangleExcessPolarizationFactorizationClosed = true

r571A2CenteredShiftOutputRadiusIdentificationClosed : Bool
r571A2CenteredShiftOutputRadiusIdentificationClosed = false

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

r571A2TriangleExcessPolarizationFactorizationClosedIsTrue :
  r571A2TriangleExcessPolarizationFactorizationClosed ≡ true
r571A2TriangleExcessPolarizationFactorizationClosedIsTrue = refl

r571A2OrderedRadialDenominatorPaymentClosedIsFalse :
  r571A2OrderedRadialDenominatorPaymentClosed ≡ false
r571A2OrderedRadialDenominatorPaymentClosedIsFalse = refl
