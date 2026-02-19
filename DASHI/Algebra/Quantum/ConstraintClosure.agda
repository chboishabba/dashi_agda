module DASHI.Algebra.Quantum.ConstraintClosure where

open import DASHI.Core.Prelude

postulate
  Constraint : Set
  _bracket_   : Constraint -> Constraint -> Constraint
  F : Constraint -> Nat

record Closure : Set where
  field
    commute : ∀ c1 c2 -> Σ Constraint (λ c3 -> (c1 bracket c2) ≡ c3)
