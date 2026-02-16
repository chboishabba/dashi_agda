module MonsterState where

open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List     using (List; []; _∷_)

------------------------------------------------------------------------
-- Factor mask (15 prime-power factors of |M|).
-- true  = keep
-- false = remove

FactorCount : Nat
FactorCount = 15

Mask : Set
Mask = List Bool

replicate : Nat → Bool → Mask
replicate zero    b = []
replicate (suc n) b = b ∷ replicate n b

fullMask : Mask
fullMask = replicate FactorCount true

emptyMask : Mask
emptyMask = replicate FactorCount false

------------------------------------------------------------------------
-- Walk state.
-- You can extend this with “window position”, “target digits”, etc.
-- For DASHI: kernel is about how masks evolve; lens decides admissibility.

record State : Set where
  constructor st
  field
    mask   : Mask
    window : Nat   -- abstract “digit window id” (moving window, index, etc.)

------------------------------------------------------------------------
-- A lens is the measurement predicate:
-- admissible s m = “removing to mask m preserves the digit window condition”.

record Lens : Set₁ where
  field
    admissible : State → Mask → Bool

------------------------------------------------------------------------
-- Candidate moves:
-- In the real system, this is “remove subsets of prime-power factors”.
-- Here we just take a finite list of candidate masks.

Candidates : Set
Candidates = List Mask
