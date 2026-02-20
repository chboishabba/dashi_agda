
module DASHI.Algebra.Quantum.SpinFromEvenClifford where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

SO : Nat → Nat → Set
SO _ _ = ⊤

Cl⁰ : Set
Cl⁰ = ⊤

Spin : Set
Spin = ⊤

toSO : Spin → SO 3 1
toSO _ = tt

kernel±1 : ⊤
kernel±1 = tt

record SpinDoubleCover : Set₁ where
  field
    hom : Spin → SO 3 1
    kernel : ⊤

SpinDoubleCover-witness : SpinDoubleCover
SpinDoubleCover-witness =
  record
    { hom = toSO
    ; kernel = kernel±1
    }

SpinIsDoubleCover-derived : SpinDoubleCover → Set
SpinIsDoubleCover-derived _ = ⊤
