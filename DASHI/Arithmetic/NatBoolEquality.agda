module DASHI.Arithmetic.NatBoolEquality where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

_≢_ : Nat → Nat → Set
x ≢ y = x ≡ y → ⊥

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc _) = false
natEq (suc _) zero = false
natEq (suc m) (suc n) = natEq m n

natEq-self : ∀ n → natEq n n ≡ true
natEq-self zero = refl
natEq-self (suc n) = natEq-self n

natEq-false⇒neq : ∀ x y → natEq x y ≡ false → x ≢ y
natEq-false⇒neq zero zero ()
natEq-false⇒neq zero (suc y) _ ()
natEq-false⇒neq (suc x) zero _ ()
natEq-false⇒neq (suc x) (suc y) eq refl = natEq-false⇒neq x y eq refl
