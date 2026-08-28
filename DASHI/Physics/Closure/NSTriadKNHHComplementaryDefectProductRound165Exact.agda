module DASHI.Physics.Closure.NSTriadKNHHComplementaryDefectProductRound165Exact where

------------------------------------------------------------------------
-- ROUND165 / PRODUCT GAIN FROM THE HH RADIAL-ANGULAR COMPLEMENTARITY
--
-- Round146 proves at square level
--
--   A + B = K,
--
-- with A = (r_p-r_q)^2, B = the scaled anti-parallel defect square, and
-- K = r_k^2.  The elementary identity
--
--   (A-B)^2 >= 0
--
-- gives the division-free product estimate
--
--   4 A B <= K^2.
--
-- This is precisely the quadratic form needed if the forcing-level double
-- commutator exposes one radial-defect factor and one angular-defect factor:
-- their product cannot exceed the low-output square, without an angle split.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelDefectSquareRound146Exact as R146

square : ℚ → ℚ
square x = x * x

four : ℚ
four = (1ℚ + 1ℚ) + (1ℚ + 1ℚ)
  where
  open import Data.Rational.Base using (1ℚ)

squareNonnegative : ∀ x → 0ℚ ≤ square x
squareNonnegative = Rational.squareNonnegative

productNonnegative : ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
productNonnegative {a} {b} aNN bNN =
  let
    instance
      aI = nonNegative aNN
      bI = nonNegative bNN
  in ℚP.nonNegative⁻¹ (a * b)

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
        (λ zero → four * (A * B) + zero ≤ four * (A * B) + square (A - B))
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
  ≤ square (R146.sq (R146.radiusK G))
hhRadialAngularProductBelowOutputFourth G radialNN angularNN =
  let
    base = fourProductBelowSumSquare
      (R146.radialGapSquared G)
      (R146.scaledAntiParallelDefectSquared G)
      radialNN angularNN

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
