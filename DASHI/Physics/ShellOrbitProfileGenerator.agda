module DASHI.Physics.ShellOrbitProfileGenerator where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List using (List; []; _∷_; length)

open import DASHI.Physics.DimensionBoundAssumptions as DBA

------------------------------------------------------------------------
-- Build a ShellOrbitProfile from a sorted (descending) list of orbit sizes.
-- This keeps the generator concrete while still allowing external data.
------------------------------------------------------------------------

profileFromSorted :
  ∀ {m : Nat} → List Nat → DBA.ShellOrbitProfile m
profileFromSorted {m} sizes =
  record
    { orbitCount = length sizes
    ; top1 = top1Of sizes
    ; top2 = top2Of sizes
    ; top3 = top3Of sizes
    }
  where
    top1Of : List Nat → Nat
    top1Of (a ∷ _) = a
    top1Of [] = 0

    top2Of : List Nat → Nat
    top2Of (_ ∷ b ∷ _) = b
    top2Of _ = 0

    top3Of : List Nat → Nat
    top3Of (_ ∷ _ ∷ c ∷ _) = c
    top3Of _ = 0
