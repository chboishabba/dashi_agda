module MonsterTraceCounts where

open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_)
open import Agda.Builtin.List     using (List; []; _∷_)

open import MonsterState
open import MonsterGroups
open import MonsterTrace

------------------------------------------------------------------------
-- If you encode digits preserved per step as Nat list:

sum : List Nat → Nat
sum []       = 0
sum (n ∷ ns) = n + sum ns

------------------------------------------------------------------------
-- Hook: you provide these for your concrete witness.
-- Option A: boundary predicate comes from the trace/table.
-- Option B: boundary predicate comes from state fields you add.

postulate
  boundary : Boundary
  digitsPerStep : List Nat

------------------------------------------------------------------------
-- Derived claims (you will later change these to concrete equalities once
-- you paste the real trace + digits list and compute the results).

groupsClaim : Nat
groupsClaim = countGroups boundary exampleTrace

digitsClaim : Nat
digitsClaim = sum digitsPerStep
