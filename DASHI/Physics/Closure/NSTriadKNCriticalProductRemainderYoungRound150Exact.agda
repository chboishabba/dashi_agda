module DASHI.Physics.Closure.NSTriadKNCriticalProductRemainderYoungRound150Exact where

------------------------------------------------------------------------
-- ROUND150 / PRODUCT-REMAINDER COMPILER FOR THE LAST A ESTIMATE
--
-- The Round104 compiler needs an integrated estimate
--
--   Production <= absorbedCoefficient * Dcrit + finiteRemainder.
--
-- A high-alpha way to obtain it is not to estimate Production directly, but
-- to expose each signed aggregate as a product of a critical-dissipation factor
-- a and a companion factor b whose square is integrable from lower-order
-- information.  Weighted Young then gives, for theta>0 and thetaInv=1/theta,
--
--   2 a b <= theta a^2 + thetaInv b^2.
--
-- This file proves that step exactly over rationals, without square roots.  It
-- therefore turns the remaining PDE discovery problem into the more precise
-- question:
--
--   can the COMPLETE signed double-commutator production be represented with
--   a companion b having a cutoff-uniform L^2_t square budget?
--
-- If yes, Round104 absorbs the theta a^2 part and the b^2 budget is the allowed
-- data/history-dependent finite-horizon remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

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
    rearrange :
      weightedYoungUpper W a b - twoAB a b
      ≡
      (theta W * thetaInv W)
        * (theta W * L2.square a)
        + thetaInv W * L2.square b
        - twoAB a b
    rearrange =
      subst
        (λ unit →
          weightedYoungUpper W a b - twoAB a b
          ≡ unit * (theta W * L2.square a)
            + thetaInv W * L2.square b - twoAB a b)
        (reciprocalLaw W)
        (solve
          (theta W ∷ thetaInv W ∷ a ∷ b ∷ []))

    factor :
      (theta W * thetaInv W)
        * (theta W * L2.square a)
        + thetaInv W * L2.square b
        - twoAB a b
      ≡ weightedYoungDefect W a b
    factor =
      solve (theta W ∷ thetaInv W ∷ a ∷ b ∷ [])
  in
  trans rearrange factor

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
      let
        identity = weightedYoungDifferenceIdentity W a b
      in
      solve
        (twoAB a b ∷ weightedYoungDefect W a b
          ∷ weightedYoungUpper W a b ∷ [])
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
