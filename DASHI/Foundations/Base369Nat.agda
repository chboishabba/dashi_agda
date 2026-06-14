module DASHI.Foundations.Base369Nat where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _==_; mod-helper)
open import Agda.Builtin.Unit using (⊤; tt)

private
  data ⊥ : Set where

  not : Bool → Bool
  not false = true
  not true  = false

  T : Bool → Set
  T false = ⊥
  T true  = ⊤

record NonZero (n : Nat) : Set where
  field
    nonZero : T (not (n == 0))

instance
  nonZero : ∀ {n} → NonZero (suc n)
  nonZero = record { nonZero = tt }

infixl 7 _%_

_%_ : (dividend divisor : Nat) .{{_ : NonZero divisor}} → Nat
m % (suc n) = mod-helper 0 n m n
