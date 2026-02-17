module DASHI.String.HilbertToy where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record InnerProductSpace : Set₁ where
  field
    V      : Set
    _+_    : V → V → V
    zero   : V
    scalar : Nat → V → V
    ⟨_,_⟩  : V → V → Nat
