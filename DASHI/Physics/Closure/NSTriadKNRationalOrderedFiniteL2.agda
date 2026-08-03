module DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz; Agda standard
-- library contributors; DASHI repository contributors.
-- Title: "Exact rational ordered carrier and finite squared
-- Cauchy--Schwarz theorem for Stage 3".
-- Venue/year: Cauchy's 1821 finite-sum inequality; Schwarz's 1888 integral
-- form; Agda standard library; DASHI formal development, 2026.
-- DOI: not applicable to the classical nineteenth-century results or this
-- repository-original finite-list formalisation.
-- Uses: the standard-library ordered field of reduced rationals, its
-- reflective commutative-ring solver, and the Gram-defect identity
--   ||a||^2 ||b||^2
--     = <a,b>^2 + sum_{i<j} (a_i b_j - a_j b_i)^2.
-- Relationship: supplies a genuine recursively defined finite dot product
-- and squared Cauchy--Schwarz theorem. It deliberately does not identify
-- rational shell arithmetic with the constructive-real non-integral H^s
-- power layer. The total rational inverse is reciprocal off zero and zero at
-- zero; none of the finite Cauchy--Schwarz argument depends on division.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Properties.Group as GroupProperties
open import Data.Integer.Base using (+0; +[1+_]; -[1+_])
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ
  using (ℚ; mkℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_; 1/_; ≢-nonZero)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; cong; cong₂; module ≡-Reasoning)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2

module AddGroup = GroupProperties ℚₚ.+-0-group

rationalInverse : ℚ → ℚ
rationalInverse (mkℚ +0 denominator coprime) = 0ℚ
rationalInverse value@(mkℚ +[1+ numerator ] denominator coprime) =
  (1/_ value {{ℚ.≢-nonZero {p = value} (λ ())}})
rationalInverse value@(mkℚ -[1+ numerator ] denominator coprime) =
  (1/_ value {{ℚ.≢-nonZero {p = value} (λ ())}})

rationalRealField : C3.RealField _
rationalRealField = record
  { Carrier = ℚ
  ; zero = 0ℚ
  ; one = 1ℚ
  ; add = _+_
  ; multiply = _*_
  ; negate = -_
  ; inverse = rationalInverse
  ; addAssociative = ℚₚ.+-assoc
  ; addCommutative = ℚₚ.+-comm
  ; addZeroLeft = ℚₚ.+-identityˡ
  ; addInverseLeft = ℚₚ.+-inverseˡ
  ; multiplyAssociative = ℚₚ.*-assoc
  ; multiplyCommutative = ℚₚ.*-comm
  ; multiplyOneLeft = ℚₚ.*-identityˡ
  ; distributeLeft = ℚₚ.*-distribˡ-+
  ; negateInvolutive = AddGroup.⁻¹-involutive
  ; negateZero = AddGroup.ε⁻¹≈ε
  }

square : ℚ → ℚ
square value = value * value

squareNonnegative : ∀ value → 0ℚ ≤ square value
squareNonnegative value with ℚₚ.≤-total 0ℚ value
... | inj₁ nonnegative =
  let
    instance
      valueNonnegative = ℚ.nonNegative nonnegative
      productNonnegative = ℚₚ.nonNeg*nonNeg⇒nonNeg value value
  in ℚₚ.nonNegative⁻¹ (value * value)
... | inj₂ nonpositive =
  let
    instance
      valueNonpositive = ℚ.nonPositive nonpositive
      productNonnegative = ℚₚ.nonPos*nonPos⇒nonNeg value value
  in ℚₚ.nonNegative⁻¹ (value * value)

addNonnegative :
  ∀ {left right} →
  0ℚ ≤ left →
  0ℚ ≤ right →
  0ℚ ≤ left + right
addNonnegative {left} {right} leftNonnegative rightNonnegative =
  subst
    (λ lower → lower ≤ left + right)
    (ℚₚ.+-identityˡ 0ℚ)
    (ℚₚ.+-mono-≤ leftNonnegative rightNonnegative)

subtractNonnegativeBelow :
  ∀ total part →
  0ℚ ≤ part →
  total - part ≤ total
subtractNonnegativeBelow total part partNonnegative =
  let
    negativePartBelowZero : - part ≤ 0ℚ
    negativePartBelowZero =
      subst
        (λ upper → - part ≤ upper)
        AddGroup.ε⁻¹≈ε
        (ℚₚ.neg-antimono-≤ partNonnegative)

    withZero : total + (- part) ≤ total + 0ℚ
    withZero = ℚₚ.+-monoʳ-≤ total negativePartBelowZero
  in
  subst
    (λ upper → total - part ≤ upper)
    (ℚₚ.+-identityʳ total)
    withZero

rationalOrderedExtension :
  L2.OrderedRealExtension rationalRealField
rationalOrderedExtension = record
  { _≤_ = _≤_
  ; leqReflexive = λ _ → ℚₚ.≤-refl
  ; leqTransitive = ℚₚ.≤-trans
  ; addMonotone = ℚₚ.+-mono-≤
  ; zeroBelowSquare = squareNonnegative
  ; zeroBelowAdd = λ {a} {b} → addNonnegative {a} {b}
  ; subtract = _-_
  ; subtractMeaning = λ _ _ → refl
  ; subtractNonnegativeBelow = λ {a} {b} → subtractNonnegativeBelow a b
  }

Pair : Set
Pair = ℚ × ℚ

pairDot : List Pair → ℚ
pairDot [] = 0ℚ
pairDot ((left , right) ∷ rest) =
  left * right + pairDot rest

leftNormSquared : List Pair → ℚ
leftNormSquared [] = 0ℚ
leftNormSquared ((left , right) ∷ rest) =
  square left + leftNormSquared rest

rightNormSquared : List Pair → ℚ
rightNormSquared [] = 0ℚ
rightNormSquared ((left , right) ∷ rest) =
  square right + rightNormSquared rest

crossSquares : ℚ → ℚ → List Pair → ℚ
crossSquares left right [] = 0ℚ
crossSquares left right ((nextLeft , nextRight) ∷ rest) =
  square (left * nextRight - right * nextLeft)
  + crossSquares left right rest

gramDefect : List Pair → ℚ
gramDefect [] = 0ℚ
gramDefect ((left , right) ∷ rest) =
  crossSquares left right rest + gramDefect rest

crossSquaresStep : ∀ left right nextLeft nextRight LN RN PD →
  (left * nextRight - right * nextLeft) * (left * nextRight - right * nextLeft) + (left * left * RN + right * right * LN - (left * right * PD + left * right * PD))
  ≡ left * left * (nextRight * nextRight + RN) + right * right * (nextLeft * nextLeft + LN) - (left * right * (nextLeft * nextRight + PD) + left * right * (nextLeft * nextRight + PD))
crossSquaresStep left right nextLeft nextRight LN RN PD =
  solve (left ∷ right ∷ nextLeft ∷ nextRight ∷ LN ∷ RN ∷ PD ∷ [])

crossSquaresExpansion :
  ∀ left right rest →
  crossSquares left right rest
  ≡
  square left * rightNormSquared rest
  + square right * leftNormSquared rest
  - ((left * right * pairDot rest) + (left * right * pairDot rest))
crossSquaresExpansion left right [] = sym (begin
  square left * 0ℚ + square right * 0ℚ - (left * right * 0ℚ + left * right * 0ℚ)
    ≡⟨ cong₂ _+_ (cong₂ _+_ (ℚₚ.*-zeroʳ (square left)) (ℚₚ.*-zeroʳ (square right)))
                 (cong -_ (cong₂ _+_ (ℚₚ.*-zeroʳ (left * right)) (ℚₚ.*-zeroʳ (left * right)))) ⟩
  0ℚ + 0ℚ - (0ℚ + 0ℚ)
    ≡⟨ refl ⟩
  0ℚ ∎)
  where open ≡-Reasoning
crossSquaresExpansion left right ((nextLeft , nextRight) ∷ rest)
  rewrite crossSquaresExpansion left right rest =
  crossSquaresStep left right nextLeft nextRight (leftNormSquared rest) (rightNormSquared rest) (pairDot rest)

finiteGramStepAlgebraic : ∀ left right LN RN PD GD →
  (left * left + LN) * (right * right + RN)
  ≡ (left * right + PD) * (left * right + PD) + (left * left * RN + right * right * LN - (left * right * PD + left * right * PD) + GD) + (LN * RN - (PD * PD + GD))
finiteGramStepAlgebraic left right LN RN PD GD =
  solve (left ∷ right ∷ LN ∷ RN ∷ PD ∷ GD ∷ [])

finiteGramStep : ∀ left right LN RN PD GD →
  LN * RN ≡ PD * PD + GD →
  (left * left + LN) * (right * right + RN)
  ≡ (left * right + PD) * (left * right + PD) + (left * left * RN + right * right * LN - (left * right * PD + left * right * PD) + GD)
finiteGramStep left right LN RN PD GD hyp
  rewrite finiteGramStepAlgebraic left right LN RN PD GD
        | hyp =
  solve (left ∷ right ∷ LN ∷ RN ∷ PD ∷ GD ∷ [])

finiteGramIdentity :
  ∀ pairs →
  leftNormSquared pairs * rightNormSquared pairs
  ≡ square (pairDot pairs) + gramDefect pairs
finiteGramIdentity [] = solve ([] : List ℚ)
finiteGramIdentity ((left , right) ∷ rest)
  rewrite crossSquaresExpansion left right rest =
  finiteGramStep left right (leftNormSquared rest) (rightNormSquared rest) (pairDot rest) (gramDefect rest) (finiteGramIdentity rest)

crossSquaresNonnegative :
  ∀ left right rest →
  0ℚ ≤ crossSquares left right rest
crossSquaresNonnegative left right [] = ℚₚ.≤-refl
crossSquaresNonnegative left right ((nextLeft , nextRight) ∷ rest) =
  addNonnegative
    (squareNonnegative (left * nextRight - right * nextLeft))
    (crossSquaresNonnegative left right rest)

gramDefectNonnegative :
  ∀ pairs → 0ℚ ≤ gramDefect pairs
gramDefectNonnegative [] = ℚₚ.≤-refl
gramDefectNonnegative ((left , right) ∷ rest) =
  addNonnegative
    (crossSquaresNonnegative left right rest)
    (gramDefectNonnegative rest)

leftNormSquaredNonnegative :
  ∀ pairs → 0ℚ ≤ leftNormSquared pairs
leftNormSquaredNonnegative [] = ℚₚ.≤-refl
leftNormSquaredNonnegative ((left , right) ∷ rest) =
  addNonnegative
    (squareNonnegative left)
    (leftNormSquaredNonnegative rest)

rightNormSquaredNonnegative :
  ∀ pairs → 0ℚ ≤ rightNormSquared pairs
rightNormSquaredNonnegative [] = ℚₚ.≤-refl
rightNormSquaredNonnegative ((left , right) ∷ rest) =
  addNonnegative
    (squareNonnegative right)
    (rightNormSquaredNonnegative rest)

finiteCauchySchwarzSquared :
  ∀ pairs →
  square (pairDot pairs)
  ≤ leftNormSquared pairs * rightNormSquared pairs
finiteCauchySchwarzSquared pairs =
  let
    addDefect :
      square (pairDot pairs)
      ≤ square (pairDot pairs) + gramDefect pairs
    addDefect =
      subst
        (λ lower →
          lower ≤ square (pairDot pairs) + gramDefect pairs)
        (ℚₚ.+-identityʳ (square (pairDot pairs)))
        (ℚₚ.+-monoʳ-≤
          (square (pairDot pairs))
          (gramDefectNonnegative pairs))
  in
  subst
    (λ upper → square (pairDot pairs) ≤ upper)
    (sym (finiteGramIdentity pairs))
    addDefect

record RestrictedPairFamily (full restricted : List Pair) : Set where
  field
    leftRestriction :
      leftNormSquared restricted ≤ leftNormSquared full
    rightRestriction :
      rightNormSquared restricted ≤ rightNormSquared full

open RestrictedPairFamily public

nonnegativeProductMonotone :
  ∀ {a b c d} →
  0ℚ ≤ a →
  0ℚ ≤ b →
  0ℚ ≤ c →
  0ℚ ≤ d →
  a ≤ c →
  b ≤ d →
  a * b ≤ c * d
nonnegativeProductMonotone {a} {b} {c} {d}
  aNonnegative bNonnegative cNonnegative dNonnegative a≤c b≤d =
  let
    instance
      aNN = ℚ.nonNegative aNonnegative
      bNN = ℚ.nonNegative bNonnegative
      cNN = ℚ.nonNegative cNonnegative
      dNN = ℚ.nonNegative dNonnegative

    first : a * b ≤ c * b
    first = ℚₚ.*-monoʳ-≤-nonNeg b a≤c

    second : c * b ≤ c * d
    second = ℚₚ.*-monoˡ-≤-nonNeg c b≤d
  in ℚₚ.≤-trans first second

finiteRestrictedCauchySchwarzSquared :
  ∀ {full restricted} →
  RestrictedPairFamily full restricted →
  square (pairDot restricted)
  ≤ leftNormSquared full * rightNormSquared full
finiteRestrictedCauchySchwarzSquared {full} {restricted} restriction =
  ℚₚ.≤-trans
    (finiteCauchySchwarzSquared restricted)
    (nonnegativeProductMonotone
      (leftNormSquaredNonnegative restricted)
      (rightNormSquaredNonnegative restricted)
      (leftNormSquaredNonnegative full)
      (rightNormSquaredNonnegative full)
      (leftRestriction restriction)
      (rightRestriction restriction))

rationalOrderedFiniteL2Closed : Bool
rationalOrderedFiniteL2Closed = true

rationalOrderedFiniteL2ClosedIsTrue :
  rationalOrderedFiniteL2Closed ≡ true
rationalOrderedFiniteL2ClosedIsTrue = refl

constructiveRealPowerBridgeStillRequired : Bool
constructiveRealPowerBridgeStillRequired = true

constructiveRealPowerBridgeStillRequiredIsTrue :
  constructiveRealPowerBridgeStillRequired ≡ true
constructiveRealPowerBridgeStillRequiredIsTrue = refl
