module DASHI.NumberTheory.Collatz.SyracuseNatModCongruenceExact where

------------------------------------------------------------------------
-- SMALL NATURAL-NUMBER MODULO CONGRUENCE COMPILER
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (NonZero)
open import Data.Nat.DivMod using (_%_; %-distribˡ-+; %-distribˡ-*)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

infix 4 _≈[_]_

_≈[_]_ : Nat → Nat → Nat → Set
left ≈[ modulus ] right = left % modulus ≡ right % modulus

modRefl :
  {modulus value : Nat} →
  value ≈[ modulus ] value
modRefl = refl

modSym :
  {modulus left right : Nat} →
  left ≈[ modulus ] right →
  right ≈[ modulus ] left
modSym = sym

modTrans :
  {modulus left middle right : Nat} →
  left ≈[ modulus ] middle →
  middle ≈[ modulus ] right →
  left ≈[ modulus ] right
modTrans = trans

fromEquality :
  {modulus left right : Nat} →
  left ≡ right →
  left ≈[ modulus ] right
fromEquality {modulus} equality = cong (_% modulus) equality

addCongruence :
  {modulus a b c d : Nat} →
  {{_ : NonZero modulus}} →
  a ≈[ modulus ] b →
  c ≈[ modulus ] d →
  (a + c) ≈[ modulus ] (b + d)
addCongruence {modulus} {a} {b} {c} {d} ab cd =
  trans
    (%-distribˡ-+ a c modulus)
    (trans
      (cong (_% modulus) (cong₂ _+_ ab cd))
      (sym (%-distribˡ-+ b d modulus)))

mulCongruence :
  {modulus a b c d : Nat} →
  {{_ : NonZero modulus}} →
  a ≈[ modulus ] b →
  c ≈[ modulus ] d →
  (a * c) ≈[ modulus ] (b * d)
mulCongruence {modulus} {a} {b} {c} {d} ab cd =
  trans
    (%-distribˡ-* a c modulus)
    (trans
      (cong (_% modulus) (cong₂ _*_ ab cd))
      (sym (%-distribˡ-* b d modulus)))

mulLeftCongruence :
  {modulus factor left right : Nat} →
  {{_ : NonZero modulus}} →
  left ≈[ modulus ] right →
  (factor * left) ≈[ modulus ] (factor * right)
mulLeftCongruence relation = mulCongruence modRefl relation

addRightCongruence :
  {modulus addend left right : Nat} →
  {{_ : NonZero modulus}} →
  left ≈[ modulus ] right →
  (left + addend) ≈[ modulus ] (right + addend)
addRightCongruence relation = addCongruence relation modRefl

------------------------------------------------------------------------
-- Translation cancellation.
--
-- Supplying an additive inverse of the translated term turns a congruence of
-- `left + addend` and `right + addend` back into a congruence of left/right.
------------------------------------------------------------------------

addCancelRightWithInverse :
  {modulus addend undo left right : Nat} →
  {{_ : NonZero modulus}} →
  (addend + undo) ≈[ modulus ] 0 →
  (left + addend) ≈[ modulus ] (right + addend) →
  left ≈[ modulus ] right
addCancelRightWithInverse {modulus} {addend} {undo} {left} {right} inverse relation =
  let
    shifted :
      ((left + addend) + undo)
      ≈[ modulus ]
      ((right + addend) + undo)
    shifted = addRightCongruence relation

    leftAssoc :
      ((left + addend) + undo)
      ≈[ modulus ]
      (left + (addend + undo))
    leftAssoc = fromEquality (NatP.+-assoc left addend undo)

    rightAssoc :
      ((right + addend) + undo)
      ≈[ modulus ]
      (right + (addend + undo))
    rightAssoc = fromEquality (NatP.+-assoc right addend undo)

    leftInverse :
      (left + (addend + undo)) ≈[ modulus ] (left + 0)
    leftInverse = addCongruence modRefl inverse

    rightInverse :
      (right + (addend + undo)) ≈[ modulus ] (right + 0)
    rightInverse = addCongruence modRefl inverse

    leftNormalize : (left + 0) ≈[ modulus ] left
    leftNormalize = fromEquality (NatP.+-identityʳ left)

    rightNormalize : (right + 0) ≈[ modulus ] right
    rightNormalize = fromEquality (NatP.+-identityʳ right)

    leftToShifted : left ≈[ modulus ] ((left + addend) + undo)
    leftToShifted =
      modSym
        (modTrans leftAssoc
          (modTrans leftInverse leftNormalize))

    shiftedToRight : ((right + addend) + undo) ≈[ modulus ] right
    shiftedToRight =
      modTrans rightAssoc
        (modTrans rightInverse rightNormalize)
  in
  modTrans leftToShifted (modTrans shifted shiftedToRight)

------------------------------------------------------------------------
-- Multiplicative unit cancellation.
------------------------------------------------------------------------

unitCancelLeft :
  {modulus u v left right : Nat} →
  {{_ : NonZero modulus}} →
  (u * v) ≈[ modulus ] 1 →
  (v * left) ≈[ modulus ] (v * right) →
  left ≈[ modulus ] right
unitCancelLeft {modulus} {u} {v} {left} {right} unit relation =
  let
    scaled :
      (u * (v * left)) ≈[ modulus ] (u * (v * right))
    scaled = mulLeftCongruence relation

    leftAssoc :
      (u * (v * left)) ≈[ modulus ] ((u * v) * left)
    leftAssoc = fromEquality (sym (NatP.*-assoc u v left))

    rightAssoc :
      (u * (v * right)) ≈[ modulus ] ((u * v) * right)
    rightAssoc = fromEquality (sym (NatP.*-assoc u v right))

    leftUnit :
      ((u * v) * left) ≈[ modulus ] (1 * left)
    leftUnit = mulCongruence unit modRefl

    rightUnit :
      ((u * v) * right) ≈[ modulus ] (1 * right)
    rightUnit = mulCongruence unit modRefl

    normalizeLeft :
      (1 * left) ≈[ modulus ] left
    normalizeLeft = fromEquality (NatP.*-identityˡ left)

    normalizeRight :
      (1 * right) ≈[ modulus ] right
    normalizeRight = fromEquality (NatP.*-identityˡ right)

    leftToScaled :
      left ≈[ modulus ] (u * (v * left))
    leftToScaled =
      modSym
        (modTrans leftAssoc
          (modTrans leftUnit normalizeLeft))

    scaledToRight :
      (u * (v * right)) ≈[ modulus ] right
    scaledToRight =
      modTrans rightAssoc
        (modTrans rightUnit normalizeRight)
  in
  modTrans leftToScaled (modTrans scaled scaledToRight)

record NatModCongruenceBoundary : Set where
  constructor natModCongruenceBoundary
  field
    additionCongruenceOwned : Nat
    multiplicationCongruenceOwned : Nat
    translationCancellationOwned : Nat
    unitCancellationOwned : Nat

canonicalNatModCongruenceBoundary : NatModCongruenceBoundary
canonicalNatModCongruenceBoundary = natModCongruenceBoundary 1 1 1 1
