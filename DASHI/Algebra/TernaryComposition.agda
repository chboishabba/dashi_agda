module DASHI.Algebra.TernaryComposition where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Trit as T

------------------------------------------------------------------------
-- Saturating composition.
--
-- This operation is useful for local cancellation and thresholded dynamics.
-- It is deliberately not advertised as ordinary integer addition: saturation
-- makes it non-associative, recorded by an explicit counterexample below.

_⊕_ : T.Trit → T.Trit → T.Trit
T.neg ⊕ T.neg = T.neg
T.neg ⊕ T.zer = T.neg
T.neg ⊕ T.pos = T.zer
T.zer ⊕ T.neg = T.neg
T.zer ⊕ T.zer = T.zer
T.zer ⊕ T.pos = T.pos
T.pos ⊕ T.neg = T.zer
T.pos ⊕ T.zer = T.pos
T.pos ⊕ T.pos = T.pos

_⊖_ : T.Trit → T.Trit → T.Trit
x ⊖ y = x ⊕ T.inv y

cancel : T.Trit → T.Trit → T.Trit
cancel = _⊕_

⊕-zeroʳ : ∀ x → x ⊕ T.zer ≡ x
⊕-zeroʳ T.neg = refl
⊕-zeroʳ T.zer = refl
⊕-zeroʳ T.pos = refl

⊕-zeroˡ : ∀ x → T.zer ⊕ x ≡ x
⊕-zeroˡ T.neg = refl
⊕-zeroˡ T.zer = refl
⊕-zeroˡ T.pos = refl

⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
⊕-comm T.neg T.neg = refl
⊕-comm T.neg T.zer = refl
⊕-comm T.neg T.pos = refl
⊕-comm T.zer T.neg = refl
⊕-comm T.zer T.zer = refl
⊕-comm T.zer T.pos = refl
⊕-comm T.pos T.neg = refl
⊕-comm T.pos T.zer = refl
⊕-comm T.pos T.pos = refl

⊕-equivariant : ∀ x y →
  T.inv (x ⊕ y) ≡ T.inv x ⊕ T.inv y
⊕-equivariant T.neg T.neg = refl
⊕-equivariant T.neg T.zer = refl
⊕-equivariant T.neg T.pos = refl
⊕-equivariant T.zer T.neg = refl
⊕-equivariant T.zer T.zer = refl
⊕-equivariant T.zer T.pos = refl
⊕-equivariant T.pos T.neg = refl
⊕-equivariant T.pos T.zer = refl
⊕-equivariant T.pos T.pos = refl

opposites-cancel : ∀ x → x ⊕ T.inv x ≡ T.zer
opposites-cancel T.neg = refl
opposites-cancel T.zer = refl
opposites-cancel T.pos = refl

self-subtracts : ∀ x → x ⊖ x ≡ T.zer
self-subtracts = opposites-cancel

record NonAssociativeWitness : Set where
  constructor witness
  field
    leftValue : (T.neg ⊕ T.neg) ⊕ T.pos ≡ T.zer
    rightValue : T.neg ⊕ (T.neg ⊕ T.pos) ≡ T.neg

nonAssociativeWitness : NonAssociativeWitness
nonAssociativeWitness = witness refl refl

------------------------------------------------------------------------
-- Exact balanced one-column addition with a carry trit.
--
-- The pair (digit , carry) denotes digit + 3*carry.  The table is the exact
-- balanced representation of sums in {-2,-1,0,1,2}; it is separate from ⊕.

record DigitCarry : Set where
  constructor dc
  field
    digit : T.Trit
    carry : T.Trit

open DigitCarry public

addCarry : T.Trit → T.Trit → DigitCarry
addCarry T.neg T.neg = dc T.pos T.neg
addCarry T.neg T.zer = dc T.neg T.zer
addCarry T.neg T.pos = dc T.zer T.zer
addCarry T.zer T.neg = dc T.neg T.zer
addCarry T.zer T.zer = dc T.zer T.zer
addCarry T.zer T.pos = dc T.pos T.zer
addCarry T.pos T.neg = dc T.zer T.zer
addCarry T.pos T.zer = dc T.pos T.zer
addCarry T.pos T.pos = dc T.neg T.pos

invDigitCarry : DigitCarry → DigitCarry
invDigitCarry (dc d c) = dc (T.inv d) (T.inv c)

addCarry-equivariant : ∀ x y →
  addCarry (T.inv x) (T.inv y) ≡ invDigitCarry (addCarry x y)
addCarry-equivariant T.neg T.neg = refl
addCarry-equivariant T.neg T.zer = refl
addCarry-equivariant T.neg T.pos = refl
addCarry-equivariant T.zer T.neg = refl
addCarry-equivariant T.zer T.zer = refl
addCarry-equivariant T.zer T.pos = refl
addCarry-equivariant T.pos T.neg = refl
addCarry-equivariant T.pos T.zer = refl
addCarry-equivariant T.pos T.pos = refl

addCarry-zeroʳ : ∀ x → addCarry x T.zer ≡ dc x T.zer
addCarry-zeroʳ T.neg = refl
addCarry-zeroʳ T.zer = refl
addCarry-zeroʳ T.pos = refl

addCarry-opposites : ∀ x → addCarry x (T.inv x) ≡ dc T.zer T.zer
addCarry-opposites T.neg = refl
addCarry-opposites T.zer = refl
addCarry-opposites T.pos = refl
