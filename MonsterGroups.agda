module MonsterGroups where

open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.List     using (List; []; _∷_)

open import MonsterState

------------------------------------------------------------------------
-- Boundary predicate: “this state ends a group”.
-- You define it from the walk semantics (or from the trace table markers).

Boundary : Set
Boundary = State → Bool

------------------------------------------------------------------------
-- Count groups in a trace given a boundary predicate.
-- Convention: group count starts at 0 for empty trace, else 1 + boundaries hit.

countGroups : Boundary → List State → Nat
countGroups b [] = 0
countGroups b (s ∷ ss) = suc (go ss)
  where
    go : List State → Nat
    go [] = 0
    go (t ∷ ts) with b t
    ... | true  = suc (go ts)
    ... | false = go ts

------------------------------------------------------------------------
-- You can similarly count “preserved digits” if your trace stores that.
-- For now keep it abstract until you add a field.
