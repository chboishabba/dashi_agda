module MonsterTrace where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List     using (List; []; _∷_)

open import MonsterState

------------------------------------------------------------------------
-- A trace is a nonempty list of states.
-- You will fill this with your table (s₀ ∷ s₁ ∷ ...).

Trace : Set
Trace = List State

------------------------------------------------------------------------
-- Example placeholder trace (replace with your real 10-group walk states).
-- Keep the structure: a list of states.

exampleTrace : Trace
exampleTrace =
  st fullMask 0 ∷
  st fullMask 1 ∷
  []
