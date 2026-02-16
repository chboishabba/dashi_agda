module MonsterTraceSound where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List     using (List; []; _∷_)

open import MonsterState
open import MonsterStep

------------------------------------------------------------------------
-- Pointwise “adjacent step” relation over a Trace.

data StepOK (L : Lens) (cands : Candidates) : List State → Set where
  ok0  : ∀ {s} → StepOK L cands (s ∷ [])
  ok∷  : ∀ {s₀ s₁ ss}
       → step L cands s₀ ≡ s₁
       → StepOK L cands (s₁ ∷ ss)
       → StepOK L cands (s₀ ∷ s₁ ∷ ss)

------------------------------------------------------------------------
-- If you have a concrete Lens and Candidates and a concrete trace,
-- this is the theorem you prove once:
--
--   traceSound : StepOK L cands trace
--
-- That’s MW-00 “orbit segments produced by step”.

-- No postulate here: you prove it for your pasted trace by refl/rewrites.
