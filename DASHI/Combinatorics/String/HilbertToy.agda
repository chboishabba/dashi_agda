module DASHI.Combinatorics.String.HilbertToy where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record InnerProductSpace : Set₁ where
  field
    V      : Set
    _V+_    : V → V → V
    zeroV   : V
    scalarV : Nat → V → V
    ⟨_,_⟩  : V → V → Nat
