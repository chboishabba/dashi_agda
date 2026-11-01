module DASHI.Algebra.Quantum.ConstraintClosure where

open import DASHI.Core.Prelude

record ConstraintClosureAxioms : Set₁ where
  field
    Constraint : Set
    _bracket_   : Constraint → Constraint → Constraint
    F : Constraint → Nat

record Closure (A : ConstraintClosureAxioms) : Set where
  field
    commute :
      ∀ c1 c2 → Σ (ConstraintClosureAxioms.Constraint A)
        (λ c3 → ConstraintClosureAxioms._bracket_ A c1 c2 ≡ c3)

open ConstraintClosureAxioms public
