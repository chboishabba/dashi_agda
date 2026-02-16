module MonsterStep where

open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List     using (List; []; _∷_)

open import MonsterState

------------------------------------------------------------------------
-- First admissible candidate (deterministic tie-break: leftmost wins).

choose : (L : Lens) → (s : State) → Candidates → Mask → Mask
choose L s []           fallback = fallback
choose L s (m ∷ ms)     fallback with Lens.admissible L s m
... | true  = m
... | false = choose L s ms fallback

------------------------------------------------------------------------
-- Step:
-- - pick next mask via lens
-- - advance window (or keep it; you decide)
-- This pins MW-00 (well-defined deterministic function).

step : (L : Lens) → Candidates → State → State
step L cands s =
  let nextMask = choose L s cands (State.mask s)
  in  st nextMask (suc (State.window s))

------------------------------------------------------------------------
-- Iteration (total, structurally terminating on Nat).

iterate : ∀ {A : Set} → (A → A) → Nat → A → A
iterate f zero    x = x
iterate f (suc n) x = iterate f n (f x)
