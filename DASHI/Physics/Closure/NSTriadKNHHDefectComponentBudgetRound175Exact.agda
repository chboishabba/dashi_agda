module DASHI.Physics.Closure.NSTriadKNHHDefectComponentBudgetRound175Exact where

------------------------------------------------------------------------
-- ROUND175 / EACH HH DEFECT COMPONENT IS PAID BY THE LOW OUTPUT
--
-- Round146 owns the exact complementarity
--
--   radialGap^2 + scaledAngularDefect^2 = r_k^2.
--
-- On the ordered rational carrier the two physical square terms are
-- nonnegative, hence EACH component is separately <= r_k^2.  Together with
-- Round165 this gives both one-component and product control without square
-- roots or an angle partition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelDefectSquareRound146Exact as R146
import DASHI.Physics.Closure.NSTriadKNHHComplementaryDefectProductRound165Exact as R165

square : ℚ → ℚ
square x = x * x

record PhysicalHHDefectNonnegativity
    (G : R146.ResonantRadiusDotGeometry Rational.rationalRealField) : Set where
  constructor physical-hh-defect-nonnegativity
  field
    radialNN : 0ℚ ≤ R146.radialGapSquared G
    angularNN : 0ℚ ≤ R146.scaledAntiParallelDefectSquared G

open PhysicalHHDefectNonnegativity public

leftComponentBelowSum :
  ∀ {left right : ℚ} →
  0ℚ ≤ right →
  left ≤ left + right
leftComponentBelowSum {left} {right} rightNN =
  subst
    (λ lower → lower ≤ left + right)
    (ℚP.+-identityʳ left)
    (ℚP.+-monoʳ-≤ left rightNN)

rightComponentBelowSum :
  ∀ {left right : ℚ} →
  0ℚ ≤ left →
  right ≤ left + right
rightComponentBelowSum {left} {right} leftNN =
  subst
    (λ lower → lower ≤ left + right)
    (ℚP.+-identityˡ right)
    (ℚP.+-monoˡ-≤ right leftNN)

radialGapSquaredBelowOutputSquare :
  (G : R146.ResonantRadiusDotGeometry Rational.rationalRealField) →
  PhysicalHHDefectNonnegativity G →
  R146.radialGapSquared G ≤ square (R146.radiusK G)
radialGapSquaredBelowOutputSquare G N =
  subst
    (λ upper → R146.radialGapSquared G ≤ upper)
    (R146.radialPlusAntiParallelDefectIsOutputSquare G)
    (leftComponentBelowSum (angularNN N))

scaledAngularDefectSquaredBelowOutputSquare :
  (G : R146.ResonantRadiusDotGeometry Rational.rationalRealField) →
  PhysicalHHDefectNonnegativity G →
  R146.scaledAntiParallelDefectSquared G ≤ square (R146.radiusK G)
scaledAngularDefectSquaredBelowOutputSquare G N =
  subst
    (λ upper → R146.scaledAntiParallelDefectSquared G ≤ upper)
    (R146.radialPlusAntiParallelDefectIsOutputSquare G)
    (rightComponentBelowSum (radialNN N))

radialAngularProductBelowOutputFourth :
  (G : R146.ResonantRadiusDotGeometry Rational.rationalRealField) →
  (N : PhysicalHHDefectNonnegativity G) →
  R165.four *
    (R146.radialGapSquared G * R146.scaledAntiParallelDefectSquared G)
  ≤ square (square (R146.radiusK G))
radialAngularProductBelowOutputFourth G N =
  R165.hhRadialAngularProductBelowOutputFourth G (radialNN N) (angularNN N)

round175RadialDefectPaidByOutputSquare : Bool
round175RadialDefectPaidByOutputSquare = true

round175AngularDefectPaidByOutputSquare : Bool
round175AngularDefectPaidByOutputSquare = true

round175ProductDefectPaidByOutputFourth : Bool
round175ProductDefectPaidByOutputFourth = true

round175SquareRootRequired : Bool
round175SquareRootRequired = false

round175PhysicalKernelL2PaymentClosed : Bool
round175PhysicalKernelL2PaymentClosed = false

round175PackageAClosed : Bool
round175PackageAClosed = false

round175RadialDefectPaidByOutputSquareIsTrue :
  round175RadialDefectPaidByOutputSquare ≡ true
round175RadialDefectPaidByOutputSquareIsTrue = refl

round175PackageAClosedIsFalse : round175PackageAClosed ≡ false
round175PackageAClosedIsFalse = refl
