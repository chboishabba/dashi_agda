module MonsterSpec where

open import Agda.Builtin.Nat      using (Nat)
open import Agda.Builtin.List     using (List)

open import MonsterState
open import MonsterStep

------------------------------------------------------------------------
-- Canonical spec = step + optional encoding function.

record Spec : Set₁ where
  field
    L     : Lens
    cands : Candidates

  stepSpec : State → State
  stepSpec = step L cands

------------------------------------------------------------------------
-- Optional: a Gödel-style encoding of state → Nat (placeholder).
-- Keep it separate: encoding is a different layer from stepping.

postulate
  encode : State → Nat
  decode : Nat → State

------------------------------------------------------------------------
-- The canonical property you’ll ultimately want:
-- decode (encode s) ≡ s  (and/or encode ∘ decode id on a domain)
