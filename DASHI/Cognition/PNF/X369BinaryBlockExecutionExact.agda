module DASHI.Cognition.PNF.X369BinaryBlockExecutionExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Binary syntax represents a repetition count without unary expansion.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F

data Count : Set where
  end : Count
  even odd : Count → Count

value : Count → Nat
value end = zero
value (even b) = value b + value b
value (odd b) = suc (value b + value b)

module Execution {State : Set} (f : State → State) where
  repeat : Nat → State → State
  repeat zero z = z
  repeat (suc n) z = repeat n (f z)

  appendRepeat : (m n : Nat) (z : State) →
    repeat (m + n) z ≡ repeat n (repeat m z)
  appendRepeat zero n z = refl
  appendRepeat (suc m) n z = appendRepeat m n (f z)

  -- Explicit composition tree; a finite signed-permutation backend
  -- can collapse each node to a fixed-size action.
  data Tree : Set where
    identity atom : Tree
    then : Tree → Tree → Tree

  run : Tree → State → State
  run identity z = z
  run atom z = f z
  run (then a b) z = run b (run a z)

  compile : Count → Tree
  compile end = identity
  compile (even b) = then (compile b) (compile b)
  compile (odd b) = then atom (then (compile b) (compile b))

  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

  correct : (b : Count) (z : State) →
    repeat (value b) z ≡ run (compile b) z
  correct end z = refl
  correct (even b) z =
    trans (appendRepeat (value b) (value b) z)
      (trans (correct b (repeat (value b) z))
        (F.cong (run (compile b)) (correct b z)))
  correct (odd b) z = correct (even b) (f z)

-- Shared compilation schedule counts one doubling and at most one
-- extra composition per digit. The expanded Tree above is not itself
-- a proof of logarithmic evaluation cost without sharing/collapse.
digits : Count → Nat
digits end = zero
digits (even b) = suc (digits b)
digits (odd b) = suc (digits b)

compositions : Count → Nat
compositions end = zero
compositions (even b) = suc (compositions b)
compositions (odd b) = suc (suc (compositions b))
