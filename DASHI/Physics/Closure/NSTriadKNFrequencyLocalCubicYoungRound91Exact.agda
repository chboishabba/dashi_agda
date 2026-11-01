module DASHI.Physics.Closure.NSTriadKNFrequencyLocalCubicYoungRound91Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- The frequency-local proof reduces the nonlinear shell contribution to three
-- weighted dyadic double sums I, II and III and then controls those sums by a
-- cubic shell mass.  The scalar mechanism is weighted Young/AM-GM.
--
-- ROUND91 / EXACT RADICAL-FREE CUBIC YOUNG CORE
--
-- For x,y,w >= 0,
--
--      3 w x y^2 <= w x^3 + 2 w y^3.
--
-- The proof is the exact factorization
--
--   x^3 + 2 y^3 - 3 x y^2 = (x-y)^2 (x+2y) >= 0.
--
-- We also lift this inequality over a finite list of weighted interactions.
-- This is the unconditional algebraic core needed when the Cheskidov--
-- Shvydkoy dyadic kernels are instantiated on the finite periodic shell
-- carrier.  No critical smallness or viscosity absorption is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

cube : ℚ → ℚ
cube x = x * x * x

two three : ℚ
two = 1ℚ + 1ℚ
three = two + 1ℚ

addNonnegative : ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
addNonnegative = ℚP.+-mono-≤

cubeNonnegative : ∀ {x : ℚ} → 0ℚ ≤ x → 0ℚ ≤ cube x
cubeNonnegative {x} xNN =
  let
    xxNN = L2.squareNonnegative x
    instance
      xxNNI = nonNegative xxNN
      xNNI = nonNegative xNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg (x * x) x
  in
  ℚP.nonNegative⁻¹ (cube x)

cubicYoungDefectFactorization : ∀ x y →
  cube x + two * cube y - three * (x * (y * y))
  ≡ (x - y) * (x - y) * (x + two * y)
cubicYoungDefectFactorization x y = solve (x ∷ y ∷ [])

cubicYoungDefectNonnegative : ∀ {x y : ℚ} →
  0ℚ ≤ x → 0ℚ ≤ y →
  0ℚ ≤ cube x + two * cube y - three * (x * (y * y))
cubicYoungDefectNonnegative {x} {y} xNN yNN =
  let
    squareNN : 0ℚ ≤ (x - y) * (x - y)
    squareNN = L2.squareNonnegative (x - y)

    twoYNN : 0ℚ ≤ two * y
    twoYNN =
      let
        twoNN : 0ℚ ≤ two
        twoNN = ℚP.+-mono-≤ ℚP.0≤1 ℚP.0≤1
        instance
          twoNNI = nonNegative twoNN
          yNNI = nonNegative yNN
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg two y
      in
      ℚP.nonNegative⁻¹ (two * y)

    sumNN : 0ℚ ≤ x + two * y
    sumNN = addNonnegative xNN twoYNN

    productNN : 0ℚ ≤ ((x - y) * (x - y)) * (x + two * y)
    productNN =
      let instance
        squareNNI = nonNegative squareNN
        sumNNI = nonNegative sumNN
        productNNI =
          ℚP.nonNeg*nonNeg⇒nonNeg
            ((x - y) * (x - y)) (x + two * y)
      in
      ℚP.nonNegative⁻¹
        (((x - y) * (x - y)) * (x + two * y))
  in
  subst
    (0ℚ ≤_)
    (symEq (cubicYoungDefectFactorization x y))
    productNN
  where
  symEq : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symEq refl = refl

threeXY2BelowCubicCharges : ∀ {x y : ℚ} →
  0ℚ ≤ x → 0ℚ ≤ y →
  three * (x * (y * y)) ≤ cube x + two * cube y
threeXY2BelowCubicCharges {x} {y} xNN yNN =
  let
    defectNN = cubicYoungDefectNonnegative xNN yNN
    shifted = ℚP.+-monoʳ-≤
      (three * (x * (y * y))) defectNN
  in
  subst
    (λ left → left ≤ cube x + two * cube y)
    (solve (x ∷ y ∷ []))
    (subst
      (λ right →
        three * (x * (y * y)) ≤ right)
      (solve (x ∷ y ∷ []))
      shifted)

weightedThreeXY2BelowCubicCharges : ∀ {w x y : ℚ} →
  0ℚ ≤ w → 0ℚ ≤ x → 0ℚ ≤ y →
  three * (w * x * (y * y))
  ≤ w * cube x + two * (w * cube y)
weightedThreeXY2BelowCubicCharges {w} {x} {y} wNN xNN yNN =
  let
    base = threeXY2BelowCubicCharges xNN yNN
    scaled :
      w * (three * (x * (y * y)))
      ≤ w * (cube x + two * cube y)
    scaled =
      let instance wNNI = nonNegative wNN
      in ℚP.*-monoˡ-≤-nonNeg w base
  in
  subst
    (λ left → left ≤ w * cube x + two * (w * cube y))
    (solve (w ∷ x ∷ y ∷ []))
    (subst
      (λ right →
        w * (three * (x * (y * y))) ≤ right)
      (solve (w ∷ x ∷ y ∷ []))
      scaled)

record WeightedCubicInteraction : Set where
  constructor weighted-cubic-interaction
  field
    weight left right : ℚ
    weightNonnegative : 0ℚ ≤ weight
    leftNonnegative : 0ℚ ≤ left
    rightNonnegative : 0ℚ ≤ right

open WeightedCubicInteraction public

interaction : WeightedCubicInteraction → ℚ
interaction cell = weight cell * left cell * (right cell * right cell)

leftCharge : WeightedCubicInteraction → ℚ
leftCharge cell = weight cell * cube (left cell)

rightCharge : WeightedCubicInteraction → ℚ
rightCharge cell = weight cell * cube (right cell)

sumInteraction : List WeightedCubicInteraction → ℚ
sumInteraction [] = 0ℚ
sumInteraction (cell ∷ cells) = interaction cell + sumInteraction cells

sumLeftCharge : List WeightedCubicInteraction → ℚ
sumLeftCharge [] = 0ℚ
sumLeftCharge (cell ∷ cells) = leftCharge cell + sumLeftCharge cells

sumRightCharge : List WeightedCubicInteraction → ℚ
sumRightCharge [] = 0ℚ
sumRightCharge (cell ∷ cells) = rightCharge cell + sumRightCharge cells

finiteWeightedCubicYoung :
  (cells : List WeightedCubicInteraction) →
  three * sumInteraction cells
  ≤ sumLeftCharge cells + two * sumRightCharge cells
finiteWeightedCubicYoung [] = ℚP.≤-refl
finiteWeightedCubicYoung (cell ∷ cells) =
  let
    head = weightedThreeXY2BelowCubicCharges
      (weightNonnegative cell)
      (leftNonnegative cell)
      (rightNonnegative cell)
    tail = finiteWeightedCubicYoung cells
    added = ℚP.+-mono-≤ head tail
  in
  subst
    (λ left → left ≤
      sumLeftCharge (cell ∷ cells) + two * sumRightCharge (cell ∷ cells))
    (solve (interaction cell ∷ sumInteraction cells ∷ []))
    (subst
      (λ right →
        three * interaction cell + three * sumInteraction cells ≤ right)
      (solve
        ( leftCharge cell ∷ sumLeftCharge cells
        ∷ rightCharge cell ∷ sumRightCharge cells ∷ []))
      added)

round91WeightedCubicYoungCoreClosed : Bool
round91WeightedCubicYoungCoreClosed = true

round91WeightedCubicYoungCoreClosedIsTrue :
  round91WeightedCubicYoungCoreClosed ≡ true
round91WeightedCubicYoungCoreClosedIsTrue = refl
