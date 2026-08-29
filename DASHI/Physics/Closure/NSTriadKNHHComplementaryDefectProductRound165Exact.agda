module DASHI.Physics.Closure.NSTriadKNHHComplementaryDefectProductRound165Exact where

------------------------------------------------------------------------
-- ROUND165 / PRODUCT GAIN FROM THE HH RADIAL-ANGULAR COMPLEMENTARITY
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelDefectSquareRound146Exact as R146

square : ℚ → ℚ
square x = x * x

four : ℚ
four = (1ℚ + 1ℚ) + (1ℚ + 1ℚ)

squareNonnegative : ∀ x → 0ℚ ≤ square x
squareNonnegative = Rational.squareNonnegative

fourProductBelowSumSquare :
  (A B : ℚ) →
  0ℚ ≤ A → 0ℚ ≤ B →
  four * (A * B) ≤ square (A + B)
fourProductBelowSumSquare A B ANN BNN =
  let
    defectNN : 0ℚ ≤ square (A - B)
    defectNN = squareNonnegative (A - B)

    algebra :
      square (A + B) ≡ four * (A * B) + square (A - B)
    algebra = solve (A ∷ B ∷ [])

    addDefect :
      four * (A * B) ≤ four * (A * B) + square (A - B)
    addDefect =
      subst
        (λ left → left ≤ four * (A * B) + square (A - B))
        (sym (ℚP.+-identityʳ (four * (A * B))))
        (ℚP.+-mono-≤ ℚP.≤-refl defectNN)
  in
  subst
    (λ upper → four * (A * B) ≤ upper)
    (sym algebra)
    addDefect

hhRadialAngularProductBelowOutputFourth :
  (G : R146.ResonantRadiusDotGeometry Rational.rationalRealField) →
  0ℚ ≤ R146.radialGapSquared G →
  0ℚ ≤ R146.scaledAntiParallelDefectSquared G →
  four *
    (R146.radialGapSquared G * R146.scaledAntiParallelDefectSquared G)
  ≤ square (square (R146.radiusK G))
hhRadialAngularProductBelowOutputFourth G radialNN angularNN =
  let
    base :
      four *
        (R146.radialGapSquared G * R146.scaledAntiParallelDefectSquared G)
      ≤ square
          (R146.radialGapSquared G + R146.scaledAntiParallelDefectSquared G)
    base = fourProductBelowSumSquare
      (R146.radialGapSquared G)
      (R146.scaledAntiParallelDefectSquared G)
      radialNN angularNN

    complement :
      R146.radialGapSquared G + R146.scaledAntiParallelDefectSquared G
      ≡ square (R146.radiusK G)
    complement = R146.radialPlusAntiParallelDefectIsOutputSquare G
  in
  subst
    (λ total →
      four *
        (R146.radialGapSquared G * R146.scaledAntiParallelDefectSquared G)
      ≤ square total)
    complement
    base

round165HHComplementaryProductGainClosed : Bool
round165HHComplementaryProductGainClosed = true

round165RequiresAnglePartition : Bool
round165RequiresAnglePartition = false

round165RequiresSquareRoot : Bool
round165RequiresSquareRoot = false

round165ForcingLevelDoubleSymbolIdentificationClosed : Bool
round165ForcingLevelDoubleSymbolIdentificationClosed = false

round165PackageAClosed : Bool
round165PackageAClosed = false

round165HHComplementaryProductGainClosedIsTrue :
  round165HHComplementaryProductGainClosed ≡ true
round165HHComplementaryProductGainClosedIsTrue = refl

round165PackageAClosedIsFalse : round165PackageAClosed ≡ false
round165PackageAClosedIsFalse = refl
