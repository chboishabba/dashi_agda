{-# OPTIONS --safe #-}
module DASHI.Interop.ExactRatioEstimateBoundary where

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl; sym)

-- Pure arithmetic representation; not empirical evidence or a prediction.
record PositiveDenominatorRatio : Set where
  constructor ratio
  field
    numerator : Nat
    denominatorPredecessor : Nat

denominator : PositiveDenominatorRatio → Nat
denominator r = suc (PositiveDenominatorRatio.denominatorPredecessor r)

infix 4 _≈_
_≈_ : PositiveDenominatorRatio → PositiveDenominatorRatio → Set
left ≈ right =
  PositiveDenominatorRatio.numerator left * denominator right ≡
  PositiveDenominatorRatio.numerator right * denominator left

ratioReflexive : (r : PositiveDenominatorRatio) → r ≈ r
ratioReflexive r = refl

ratioSymmetric : (left right : PositiveDenominatorRatio) →
  left ≈ right → right ≈ left
ratioSymmetric left right proof = sym proof

sameRepresentation : (n d : Nat) → ratio n d ≈ ratio n d
sameRepresentation n d = refl
