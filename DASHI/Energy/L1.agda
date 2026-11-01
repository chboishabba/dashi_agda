module DASHI.Energy.L1 where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Energy.Core

record AddAbs {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    _+_ : A → A → A
    abs : A → A

record L1Structure {ℓa ℓv}
  (A : Set ℓa) (V : Set ℓv)
  : Set (lsuc (ℓa ⊔ ℓv)) where
  field
    AA : AddAbs A
    dim : Nat
    coord : V → Nat → A
    fold : (Nat → A) → A
    L1 : V → A

open AddAbs public
open L1Structure public
