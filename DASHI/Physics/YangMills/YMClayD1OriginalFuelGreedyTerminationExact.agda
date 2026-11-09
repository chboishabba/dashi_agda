module DASHI.Physics.YangMills.YMClayD1OriginalFuelGreedyTerminationExact where

------------------------------------------------------------------------
-- Total fuel-indexed ORIGINAL source-star greedy construction.
-- This directly addresses the termination-checking risk of recursion
-- through filterOriginalStarFree in the original un-fuelled definition.
--
-- It consumes the ACTUAL source link-star decision/filter, never a
-- synthetic geometry, probability kernel or postulated degree bound.
-- It proves independence and input-subset for every fuel.
--
-- It does NOT yet prove that fuel=length(input) computes the same
-- extensional list as the earlier un-fuelled greedy declaration;
-- that requires the filter-length monotonicity induction.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayD1OriginalPlaquetteSupportDecisionExact as Original

fuelGreedyOriginalDisjointStars :
  ∀ {n} → Nat → List (Original.Bond n) → List (Original.Bond n)
fuelGreedyOriginalDisjointStars zero marked = []
fuelGreedyOriginalDisjointStars (suc fuel) [] = []
fuelGreedyOriginalDisjointStars (suc fuel) (a ∷ as) =
  a ∷ fuelGreedyOriginalDisjointStars fuel
    (Original.filterOriginalStarFree a as)

fuelGreedyOriginalSubset :
  ∀ {n} (fuel : Nat) (as : List (Original.Bond n))
    (b : Original.Bond n) →
  Torus._∈_ b (fuelGreedyOriginalDisjointStars fuel as) →
  Torus._∈_ b as
fuelGreedyOriginalSubset zero as b ()
fuelGreedyOriginalSubset (suc fuel) [] b ()
fuelGreedyOriginalSubset (suc fuel) (a ∷ as) b Torus.here =
  Torus.here
fuelGreedyOriginalSubset (suc fuel) (a ∷ as) b
  (Torus.there selectedTail) =
  Torus.there
    (Original.filterOriginalStarFreeSubset a as
      (fuelGreedyOriginalSubset fuel
        (Original.filterOriginalStarFree a as)
        b selectedTail))

fuelGreedyOriginalIndependent :
  ∀ {n} (fuel : Nat) (as : List (Original.Bond n)) →
  Original.AllOriginalStarsIndependent
    (fuelGreedyOriginalDisjointStars fuel as)
fuelGreedyOriginalIndependent zero as = Original.noStars
fuelGreedyOriginalIndependent (suc fuel) [] = Original.noStars
fuelGreedyOriginalIndependent (suc fuel) (a ∷ as) =
  Original.addFreeStar
    (λ b selected →
      Original.filterOriginalStarFreeSound a as b
        (fuelGreedyOriginalSubset fuel
          (Original.filterOriginalStarFree a as)
          b selected))
    (fuelGreedyOriginalIndependent fuel
      (Original.filterOriginalStarFree a as))
