module MonsterVectors where

open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.List     using (List; []; _∷_)

open import MonsterState

------------------------------------------------------------------------
-- Minimal conformance vectors:
-- (input state, expected next state)

record Vector : Set where
  constructor vec
  field
    input  : State
    output : State

Vectors : Set
Vectors = List Vector

-- Fill with concrete examples once your step spec is pinned.
vectors : Vectors
vectors = []
