module AntiFascistSystem where

open import Level
open import Data.Nat
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality

postulate
  S : Set
  H : S → ℕ

-- Invertible operator

record Invertible : Set where
  field
    U    : S → S
    U⁻¹  : S → S
    left  : ∀ s → U⁻¹ (U s) ≡ s
    right : ∀ s → U (U⁻¹ s) ≡ s

-- Entropy preserved under unitary-like operator

postulate
  entropy-preserved :
    ∀ (u : Invertible) s → H (Invertible.U u s) ≡ H s

-- No monotone collapse

postulate
  non-collapse :
    ∀ (u : Invertible) → ¬ (∀ s → H (Invertible.U u s) ≤ H s)
