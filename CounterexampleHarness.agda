module CounterexampleHarness where

open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Relation.Nullary.Negation using (¬_)


------------------------------------------------------------------------
-- Generic falsifier

record Counterexample {A : Set}
                      (P : A → Set)
                      : Set₁ where
  field
    witness : A
    violates : ¬ P witness
