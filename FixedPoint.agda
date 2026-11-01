module FixedPoint where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Ultrametric as UMetric
open import Contraction

------------------------------------------------------------------------
-- Fixed point definition

Fixed : {S : Set} → (S → S) → S → Set
Fixed K x = K x ≡ x

------------------------------------------------------------------------
-- Uniqueness of fixed point under contraction

record UniqueFixed
       {S : Set}
       (U : UMetric.Ultrametric S)
       (K : S → S)
       (C : Contractive U K)
       : Set where

  open UMetric.Ultrametric U
  open Contractive C

  field
    unique :
      ∀ x y →
      Fixed K x →
      Fixed K y →
      x ≡ y
