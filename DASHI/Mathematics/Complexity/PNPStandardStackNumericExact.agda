module DASHI.Mathematics.Complexity.PNPStandardStackNumericExact where

-- Actual source split-list carrier and exact extent retention.
-- The executable compiler uses the corresponding base-B numeric pops;
-- this source weld records the actual source transition identities
-- without replacing StandardConfiguration with an unrelated tape model.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as S
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L

module Stack {State Symbol : Set}
    (machine : S.StandardSingleTapeMachine State Symbol)
    (B : Nat) (digit : Symbol → Nat)
    (blankZero : digit (S.blank machine) ≡ zero) where

  value : List Symbol → Nat
  value [] = zero
  value (a ∷ as) = digit a + B * value as

  length : List Symbol → Nat
  length [] = zero
  length (_ ∷ as) = suc (length as)

  head : List Symbol → Symbol
  head [] = S.blank machine
  head (a ∷ as) = a

  tail : List Symbol → List Symbol
  tail [] = []
  tail (a ∷ as) = as

  data Packed : Set where
    packed : State → Nat → Nat → Nat → Nat → Packed

  pack : S.StandardConfiguration machine → Packed
  pack (S.standard-configuration l q a r) =
    packed q (value l) (value (a ∷ r)) (length l) (suc (length r))

  -- Exact stack pop decomposition, including the empty blank extension.
  popShape : ∀ xs → value xs ≡ digit (head xs) + B * value (tail xs)
  popShape [] rewrite blankZero = zeroRight B
    where
      zeroRight : ∀ n → zero ≡ zero + n * zero
      zeroRight zero = refl
      zeroRight (suc n) = zeroRight n
  popShape (a ∷ as) = refl

  rightExtent : List Symbol → Nat
  rightExtent [] = suc zero
  rightExtent (_ ∷ rs) = suc (length rs)

  moveRightExact : ∀ l q a r q' b →
    pack (S.standardApplyTransition machine
      (S.standard-configuration l q a r)
      (S.standard-transition q' b L.moveRight))
    ≡ packed q' (value (b ∷ l)) (value r) (suc (length l)) (rightExtent r)
  moveRightExact l q a [] q' b rewrite blankZero = blankValue
    where
      blankValue : packed q' (value (b ∷ l)) (zero + B * zero)
        (suc (length l)) (suc zero) ≡
        packed q' (value (b ∷ l)) zero (suc (length l)) (suc zero)
      blankValue = congR B
        where
          congR : ∀ n → packed q' (value (b ∷ l)) (zero + n * zero)
            (suc (length l)) (suc zero) ≡
            packed q' (value (b ∷ l)) zero (suc (length l)) (suc zero)
          congR zero = refl
          congR (suc n) = congR n
  moveRightExact l q a (r ∷ rs) q' b = refl

  moveLeftExact : ∀ l q a r q' b →
    pack (S.standardApplyTransition machine
      (S.standard-configuration l q a r)
      (S.standard-transition q' b L.moveLeft))
    ≡ packed q' (value (tail l)) (value (head l ∷ b ∷ r))
        (length (tail l)) (suc (suc (length r)))
  moveLeftExact [] q a r q' b = refl
  moveLeftExact (l ∷ ls) q a r q' b = refl

  stayExact : ∀ l q a r q' b →
    pack (S.standardApplyTransition machine
      (S.standard-configuration l q a r)
      (S.standard-transition q' b L.stayPut))
    ≡ packed q' (value l) (value (b ∷ r)) (length l) (suc (length r))
  stayExact l q a r q' b = refl

-- Native numeric quotient/remainder reification, digit-code inverse and
-- raw FRACTRAN priority transport still need their cross-module weld.
