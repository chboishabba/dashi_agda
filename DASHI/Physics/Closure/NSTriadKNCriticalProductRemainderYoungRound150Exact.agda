module DASHI.Physics.Closure.NSTriadKNCriticalProductRemainderYoungRound150Exact where

------------------------------------------------------------------------
-- ROUND150 / PRODUCT-REMAINDER COMPILER FOR THE LAST A ESTIMATE
--
-- The Round104 compiler needs
--
--   Production <= absorbedCoefficient * Dcrit + finiteRemainder.
--
-- If a signed aggregate is bounded by 2ab, with a the critical-dissipation
-- factor and b a companion whose square has a cutoff-uniform time budget,
-- weighted Young gives
--
--   2ab <= theta a^2 + theta^{-1} b^2.
--
-- The proof below is exact over rationals and needs no square-root operation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record PositiveReciprocalWeight : Set where
  constructor positive-reciprocal-weight
  field
    theta thetaInv : ℚ
    thetaNonnegative : 0ℚ ≤ theta
    thetaInvNonnegative : 0ℚ ≤ thetaInv
    reciprocalLaw : theta * thetaInv ≡ 1ℚ

open PositiveReciprocalWeight public

twoAB : ℚ → ℚ → ℚ
twoAB a b = a * b + a * b

weightedYoungUpper : PositiveReciprocalWeight → ℚ → ℚ → ℚ
weightedYoungUpper W a b =
  theta W * L2.square a + thetaInv W * L2.square b

weightedYoungDefect : PositiveReciprocalWeight → ℚ → ℚ → ℚ
weightedYoungDefect W a b =
  thetaInv W * L2.square (theta W * a - b)

weightedYoungDefectNonnegative :
  (W : PositiveReciprocalWeight) (a b : ℚ) →
  0ℚ ≤ weightedYoungDefect W a b
weightedYoungDefectNonnegative W a b =
  let
    instance
      invNN = nonNegative (thetaInvNonnegative W)
      sqNN = nonNegative (L2.squareNonnegative (theta W * a - b))
      productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg
        (thetaInv W) (L2.square (theta W * a - b))
  in
  ℚₚ.nonNegative⁻¹ (weightedYoungDefect W a b)

weightedYoungDifferenceIdentity :
  (W : PositiveReciprocalWeight) (a b : ℚ) →
  weightedYoungUpper W a b - twoAB a b
  ≡ weightedYoungDefect W a b
weightedYoungDifferenceIdentity W a b =
  let
    t = theta W
    i = thetaInv W
    unitLaw = reciprocalLaw W

    unitized :
      weightedYoungUpper W a b - twoAB a b
      ≡
      (t * i) * (t * L2.square a)
      + i * L2.square b
      - (t * i) * twoAB a b
    unitized =
      trans
        (solve (t ∷ i ∷ a ∷ b ∷ []))
        (cong
          (λ unit →
            unit * (t * L2.square a)
            + i * L2.square b
            - unit * twoAB a b)
          (sym unitLaw))

    factorized :
      (t * i) * (t * L2.square a)
      + i * L2.square b
      - (t * i) * twoAB a b
      ≡ weightedYoungDefect W a b
    factorized = solve (t ∷ i ∷ a ∷ b ∷ [])
  in
  trans unitized factorized

weightedYoung :
  (W : PositiveReciprocalWeight) (a b : ℚ) →
  twoAB a b ≤ weightedYoungUpper W a b
weightedYoung W a b =
  let
    defectNN = weightedYoungDefectNonnegative W a b

    shifted :
      twoAB a b + 0ℚ
      ≤ twoAB a b + weightedYoungDefect W a b
    shifted = ℚₚ.+-monoʳ-≤ (twoAB a b) defectNN

    leftMeaning : twoAB a b + 0ℚ ≡ twoAB a b
    leftMeaning = ℚₚ.+-identityʳ (twoAB a b)

    rightMeaning :
      twoAB a b + weightedYoungDefect W a b
      ≡ weightedYoungUpper W a b
    rightMeaning =
      trans
        (cong (twoAB a b +_)
          (sym (weightedYoungDifferenceIdentity W a b)))
        (solve (twoAB a b ∷ weightedYoungUpper W a b ∷ []))
  in
  subst
    (λ left → left ≤ twoAB a b + weightedYoungDefect W a b)
    leftMeaning
    (subst
      (λ right → twoAB a b ≤ right)
      rightMeaning
      shifted)

record CriticalProductPaymentCell : Set where
  constructor critical-product-payment-cell
  field
    weight : PositiveReciprocalWeight
    dissipationRoot companion : ℚ
    signedProduction : ℚ
    productionProductBound :
      signedProduction ≤ twoAB dissipationRoot companion

open CriticalProductPaymentCell public

criticalProductCellPaysIntoSquareBudgets :
  (C : CriticalProductPaymentCell) →
  signedProduction C
  ≤ weightedYoungUpper (weight C) (dissipationRoot C) (companion C)
criticalProductCellPaysIntoSquareBudgets C =
  ℚₚ.≤-trans
    (productionProductBound C)
    (weightedYoung (weight C) (dissipationRoot C) (companion C))

round150WeightedYoungWithoutSquareRootsClosed : Bool
round150WeightedYoungWithoutSquareRootsClosed = true

round150RemainingAProblemIsCompanionL2Budget : Bool
round150RemainingAProblemIsCompanionL2Budget = true

round150PackageAClosed : Bool
round150PackageAClosed = false

round150WeightedYoungWithoutSquareRootsClosedIsTrue :
  round150WeightedYoungWithoutSquareRootsClosed ≡ true
round150WeightedYoungWithoutSquareRootsClosedIsTrue = refl

round150PackageAClosedIsFalse : round150PackageAClosed ≡ false
round150PackageAClosedIsFalse = refl
