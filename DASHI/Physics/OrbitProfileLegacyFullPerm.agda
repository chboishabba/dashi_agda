module DASHI.Physics.OrbitProfileLegacyFullPerm where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.List using (List; _∷_; [])

open import DASHI.Physics.DimensionBoundAssumptions as DBA
open import DASHI.Physics.ShellOrbitProfileGenerator as SOPG

-- Concrete external profile for m = 6 (one-minus signature pattern).
-- Values taken from the external orbit-profile scan.

m′ : Nat
m′ = 5

m : Nat
m = suc m′

orbitProfile-m6 : DBA.ShellOrbitProfile m
orbitProfile-m6 =
  SOPG.profileFromSorted {m = m} orbitSizes
  where
    -- Sorted descending sizes from the external orbit-profile scan.
    orbitSizes : List Nat
    orbitSizes = 80 ∷ 10 ∷ 2 ∷ []

------------------------------------------------------------------------
-- Additional external profiles for the (1, m-1) family (from the scan)
------------------------------------------------------------------------

orbitProfile-m2 : DBA.ShellOrbitProfile 2
orbitProfile-m2 =
  SOPG.profileFromSorted {m = 2} (2 ∷ 2 ∷ [])

orbitProfile-m3 : DBA.ShellOrbitProfile 3
orbitProfile-m3 =
  SOPG.profileFromSorted {m = 3} (8 ∷ 4 ∷ 2 ∷ [])

orbitProfile-m4 : DBA.ShellOrbitProfile 4
orbitProfile-m4 =
  SOPG.profileFromSorted {m = 4} (24 ∷ 6 ∷ 2 ∷ [])

orbitProfile-m5 : DBA.ShellOrbitProfile 5
orbitProfile-m5 =
  SOPG.profileFromSorted {m = 5} (48 ∷ 8 ∷ 2 ∷ [])

orbitProfile-m7 : DBA.ShellOrbitProfile 7
orbitProfile-m7 =
  SOPG.profileFromSorted {m = 7} (120 ∷ 12 ∷ 2 ∷ [])

orbitProfile-m8 : DBA.ShellOrbitProfile 8
orbitProfile-m8 =
  SOPG.profileFromSorted {m = 8} (168 ∷ 14 ∷ 2 ∷ [])
