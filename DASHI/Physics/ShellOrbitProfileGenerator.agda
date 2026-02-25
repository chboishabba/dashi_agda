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
  let
    top1 : Nat
    top1 with sizes
    ... | a ∷ _ = a
    ... | []    = 0

    top2 : Nat
    top2 with sizes
    ... | _ ∷ b ∷ _ = b
    ... | _         = 0

    top3 : Nat
    top3 with sizes
    ... | _ ∷ _ ∷ c ∷ _ = c
    ... | _             = 0
  in
  record
    { orbitCount = length sizes
    ; top1 = top1
    ; top2 = top2
    ; top3 = top3
    }
