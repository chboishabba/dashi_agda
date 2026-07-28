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
-- and squared Cauchy--Schwarz theorem.  It deliberately does not identify
-- rational shell arithmetic with the constructive-real non-integral H^s
-- power layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Properties.Group as GroupProperties
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2

module AddGroup = GroupProperties ℚₚ.+-0-group

------------------------------------------------------------------------
-- Concrete rational RealField and order extension.
------------------------------------------------------------------------

rationalRealField : C3.RealField _
rationalRealField = record
  { Carrier = ℚ
  ; zero = 0ℚ
  ; one = 1ℚ
  ; add = _+_
  ; multiply = _*_
  ; negate = -_
  ; inverse = λ _ → 0ℚ
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
      valueNonnegative = ℚₚ.nonNegative nonnegative
      productNonnegative = ℚₚ.nonNeg*nonNeg⇒nonNeg value value
  in ℚₚ.nonNegative⁻¹ (value * value)
... | inj₂ nonpositive =
  let
    instance
      valueNonpositive = ℚₚ.nonPositive nonpositive
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
    withZero = ℚₚ.+-mono-≤ ℚₚ.≤-refl negativePartBelowZero
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
  ; subtractNonnegativeBelow = subtractNonnegativeBelow
  }

------------------------------------------------------------------------
-- Actual finite dot product and Gram-defect development.
------------------------------------------------------------------------

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

crossSquaresExpansion :
  ∀ left right rest →
  crossSquares left right rest
  ≡
  square left * rightNormSquared rest
  + square right * leftNormSquared rest
  - ((left * right * pairDot rest) + (left * right * pairDot rest))
crossSquaresExpansion left right [] =
  solve (left ∷ right ∷ [])
crossSquaresExpansion left right ((nextLeft , nextRight) ∷ rest)
  rewrite crossSquaresExpansion left right rest =
  solve
    ( left ∷ right ∷ nextLeft ∷ nextRight
    ∷ leftNormSquared rest ∷ rightNormSquared rest
    ∷ pairDot rest ∷ [] )

finiteGramIdentity :
  ∀ pairs →
  leftNormSquared pairs * rightNormSquared pairs
  ≡ square (pairDot pairs) + gramDefect pairs
finiteGramIdentity [] = solve []
finiteGramIdentity ((left , right) ∷ rest)
  rewrite finiteGramIdentity rest
        | crossSquaresExpansion left right rest =
  solve
    ( left ∷ right ∷ leftNormSquared rest
    ∷ rightNormSquared rest ∷ pairDot rest
    ∷ gramDefect rest ∷ [] )

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
        (ℚₚ.+-mono-≤
          ℚₚ.≤-refl
          (gramDefectNonnegative pairs))
  in
  subst
    (λ upper → square (pairDot pairs) ≤ upper)
    (sym (finiteGramIdentity pairs))
    addDefect

------------------------------------------------------------------------
-- Restricting support only decreases the two nonnegative squared norms.
------------------------------------------------------------------------

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
      aNN = ℚₚ.nonNegative aNonnegative
      bNN = ℚₚ.nonNegative bNonnegative
      cNN = ℚₚ.nonNegative cNonnegative
      dNN = ℚₚ.nonNegative dNonnegative

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
