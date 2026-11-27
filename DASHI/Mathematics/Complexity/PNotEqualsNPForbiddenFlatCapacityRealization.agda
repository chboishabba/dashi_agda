module DASHI.Mathematics.Complexity.PNotEqualsNPForbiddenFlatCapacityRealization where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

not : Bool → Bool
not false = true
not true = false

xor : Bool → Bool → Bool
xor false b = b
xor true b = not b

or : Bool → Bool → Bool
or false b = b
or true b = true

bit : Bool → Nat
bit false = 0
bit true = 1

weight : Bool → Bool → Nat
weight p q = bit (not p) + bit (not q) + bit (not (xor p q))

target : Bool → Bool → Nat
target false false = 3
target _ _ = 1

weightExact : ∀ p q → weight p q ≡ target p q
weightExact false false = refl
weightExact false true = refl
weightExact true false = refl
weightExact true true = refl

nae : Bool → Bool → Bool → Bool
nae a b c = or (xor a b) (xor b c)

and : Bool → Bool → Bool
and false b = false
and true b = b

split : Bool → Bool → Bool → Bool → Bool
split a b c t = and (nae a b t) (nae (not t) c false)

-- Exact existential projection of the fresh split bit.
splitExact : ∀ a b c → or (split a b c false) (split a b c true) ≡ or (or a b) c
splitExact false false false = refl
splitExact false false true = refl
splitExact false true false = refl
splitExact false true true = refl
splitExact true false false = refl
splitExact true false true = refl
splitExact true true false = refl
splitExact true true true = refl
