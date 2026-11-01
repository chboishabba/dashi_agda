{-# OPTIONS --safe #-}
module DASHI.Physics.Constraints.Generators where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)

record ConstraintSystem : Set₁ where
  field
    Constraint : Set
    actsOn     : Set → Set
    apply      : ∀ {S : Set} → Constraint → S → S
open ConstraintSystem public
