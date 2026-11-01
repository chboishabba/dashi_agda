{-# OPTIONS --safe #-}
module DASHI.Physics.Constraints.Closure where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Constraints.Generators
open import DASHI.Physics.Constraints.Bracket

record ClosureLaw (CS : ConstraintSystem) (L : LieLike CS) : Set₁ where
  open ConstraintSystem CS
  open LieLike L
  field
    closes : ∀ c₁ c₂ →
      Σ (ConstraintSystem.Constraint CS)
        (λ c₃ → LieLike._[_,]_ L c₁ c₂ ≡ c₃)
