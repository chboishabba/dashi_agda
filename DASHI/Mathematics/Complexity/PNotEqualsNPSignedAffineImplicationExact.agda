module DASHI.Mathematics.Complexity.PNotEqualsNPSignedAffineImplicationExact where

-- Scope-preserving proof rules for the signed capacity collector.
-- Normal addition/evaluation is supplied by the original affine carrier.
-- No completeness, cost or SAT decision premise is asserted.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; <-irrefl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

flip : Bool → Bool
flip false = true
flip true = false

xor : Bool → Bool → Bool
xor false b = b
xor true b = flip b

oppositeBit : (a b : Bool) → (a ≡ b → ⊥) → a ≡ flip b
oppositeBit false false no = ⊥-elim (no refl)
oppositeBit false true no = refl
oppositeBit true false no = refl
oppositeBit true true no = ⊥-elim (no refl)

module Rules (State Normal : Set)
             (eval : Normal → State → Bool)
             (add : Normal → Normal → Normal)
             (evalAdd : ∀ a b z → eval (add a b) z ≡ xor (eval a z) (eval b z))
             where
  record Literal : Set where
    constructor literal
    field
      normal : Normal
      bit : Bool
  open Literal public

  Holds : Literal → State → Set
  Holds l z = eval (normal l) z ≡ bit l

  opposite : Literal → Literal
  opposite l = literal (normal l) (flip (bit l))

  Entails : (State → Set) → Literal → Set
  Entails S l = ∀ z → S z → Holds l z

  Excludes : (State → Set) → Literal → Literal → Set
  Excludes S a b = ∀ z → S z → Holds a z → Holds b z → ⊥

  -- Each excluded orientation supplies both signed implications.
  unit : ∀ {S a b} → Excludes S a b → Entails S a → Entails S (opposite b)
  unit {b = b} no yes z hz =
    oppositeBit (eval (normal b) z) (bit b) (no z hz (yes z hz))

  reverseUnit : ∀ {S a b} → Excludes S a b → Entails S b → Entails S (opposite a)
  reverseUnit {a = a} no yes z hz =
    oppositeBit (eval (normal a) z) (bit a) (λ ha → no z hz ha (yes z hz))

  sumLiteral : Literal → Literal → Literal
  sumLiteral a b = literal (add (normal a) (normal b)) (xor (bit a) (bit b))

  -- This is the dependency information lost by independent Boolean 2-SAT.
  xorSound : ∀ {S a b} → Entails S a → Entails S b → Entails S (sumLiteral a b)
  xorSound {a = a} {b = b} pa pb z hz =
    trans (evalAdd (normal a) (normal b) z) (cong₂ xor (pa z hz) (pb z hz))

  -- An arbitrary-rank conditional derivation may be discharged at its seed.
  refute : ∀ {S a} → (∀ z → S z → Holds a z → ⊥) → Entails S (opposite a)
  refute {a = a} no z hz =
    oppositeBit (eval (normal a) z) (bit a) (no z hz)

  conditionedFloor : ∀ {S a} (weight : State → ℕ) (cap lo : ℕ) →
    (∀ z → S z → weight z ≤ cap) →
    (∀ z → S z → Holds a z → lo ≤ weight z) →
    cap < lo → Entails S (opposite a)
  conditionedFloor weight cap lo upper lower strict =
    refute (λ z hz ha → <-irrefl refl (≤-trans strict (≤-trans (lower z hz ha) (upper z hz))))
