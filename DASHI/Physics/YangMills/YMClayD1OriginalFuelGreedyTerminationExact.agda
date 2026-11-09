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

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; +-mono-≤)
open import Data.Sum using (inj₁; inj₂)
open import Agda.Builtin.Sigma using (Σ; _,_) 
import DASHI.Physics.YangMills.YMClayD1OriginalPeriodicPlaquetteFourBondSupportExact as Source
import DASHI.Physics.YangMills.YMClayD1OriginalGreedy19CountingExact as Count

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

------------------------------------------------------------------------
-- Native filter decreases or preserves list length, proved by direct
-- structural recursion on the ORIGINAL input list.
------------------------------------------------------------------------

leWeakenRight : ∀ {a b : Nat} → a ≤ b → a ≤ suc b
leWeakenRight z≤n = z≤n
leWeakenRight (s≤s bound) = s≤s (leWeakenRight bound)

filterOriginalStarLengthBound :
  ∀ {n} (a : Original.Bond n) (as : List (Original.Bond n)) →
  Source.length (Original.filterOriginalStarFree a as) ≤ Source.length as
filterOriginalStarLengthBound a [] = z≤n
filterOriginalStarLengthBound a (b ∷ bs)
  with Original.decideOriginalStarsDisjoint a b
... | Torus.yes _ = s≤s (filterOriginalStarLengthBound a bs)
... | Torus.no _ = leWeakenRight (filterOriginalStarLengthBound a bs)

sucBoundInverse : ∀ {a b : Nat} → suc a ≤ suc b → a ≤ b
sucBoundInverse (s≤s bound) = bound

-- No fuel exhaustion on a list of at most 'fuel' bonds.
fuelGreedyOriginalMaximal :
  ∀ {n} (fuel : Nat) (marked : List (Original.Bond n))
    (b : Original.Bond n) →
  Source.length marked ≤ fuel →
  Torus._∈_ b marked →
  Original.OriginalStarDominated b
    (fuelGreedyOriginalDisjointStars fuel marked)
fuelGreedyOriginalMaximal zero [] b lengthBound ()
fuelGreedyOriginalMaximal zero (a ∷ as) b () inMarked
fuelGreedyOriginalMaximal (suc fuel) [] b lengthBound ()
fuelGreedyOriginalMaximal (suc fuel) (a ∷ as) b
  lengthBound Torus.here = inj₁ Torus.here
fuelGreedyOriginalMaximal (suc fuel) (a ∷ as) b
  lengthBound (Torus.there inTail)
  with Original.decideOriginalStarsDisjoint a b
... | Torus.no conflict =
  inj₂ (a , Torus.pair Torus.here conflict)
... | Torus.yes separate
  with fuelGreedyOriginalMaximal
    fuel (Original.filterOriginalStarFree a as) b
    (≤-trans
      (filterOriginalStarLengthBound a as)
      (sucBoundInverse lengthBound))
    (Original.filterOriginalStarFreeComplete a as b inTail separate)
... | inj₁ selected =
  inj₁ (Torus.there selected)
... | inj₂ (chosen , evidence) =
  inj₂ (chosen , Torus.pair
    (Torus.there (Torus.first evidence))
    (Torus.second evidence))

fuelGreedyWithFullLengthIsMaximal :
  ∀ {n} (marked : List (Original.Bond n))
    (b : Original.Bond n) →
  Torus._∈_ b marked →
  Original.OriginalStarDominated b
    (fuelGreedyOriginalDisjointStars (Source.length marked) marked)
fuelGreedyWithFullLengthIsMaximal marked b member =
  fuelGreedyOriginalMaximal
    (Source.length marked) marked b ≤-refl member

-- The old 19-count interface's degree source is reused, not replaced.
-- This proof is structurally recursive in fuel, avoiding the potentially
-- nonterminating recursive definition in the un-fuelled transport.

fuelGreedyOriginal19Packing :
  (degree : Count.OriginalStar18RemovalBound) →
  ∀ {n} (fuel : Nat) (marked : List (Original.Bond n)) →
  Source.length marked ≤ fuel →
  Count.DistinctMarked marked →
  Source.length marked ≤
    Count.nineteenTimes
      (Source.length (fuelGreedyOriginalDisjointStars fuel marked))
fuelGreedyOriginal19Packing degree zero [] lengthBound Count.distinctNil =
  z≤n
fuelGreedyOriginal19Packing degree zero (a ∷ as) () distinct
fuelGreedyOriginal19Packing degree (suc fuel) [] lengthBound Count.distinctNil =
  z≤n
fuelGreedyOriginal19Packing degree (suc fuel) (a ∷ as)
  lengthBound (Count.distinctCons absent tailDistinct) =
  s≤s
    (≤-trans
      (Count.originalDistinctStarRemovalBound degree a as
        (Count.distinctCons absent tailDistinct))
      (+-mono-≤ ≤-refl
        (fuelGreedyOriginal19Packing degree
          fuel (Original.filterOriginalStarFree a as)
          (≤-trans
            (filterOriginalStarLengthBound a as)
            (sucBoundInverse lengthBound))
          (Count.filterOriginalStarFreePreservesDistinct
            a as tailDistinct))))

fuelGreedyOriginal19PackingFullLength :
  (degree : Count.OriginalStar18RemovalBound) →
  ∀ {n} (marked : List (Original.Bond n)) →
  Count.DistinctMarked marked →
  Source.length marked ≤
    Count.nineteenTimes
      (Source.length
        (fuelGreedyOriginalDisjointStars (Source.length marked) marked))
fuelGreedyOriginal19PackingFullLength degree marked distinct =
  fuelGreedyOriginal19Packing
    degree (Source.length marked) marked ≤-refl distinct

------------------------------------------------------------------------
-- Full-input fuel exhaustiveness / extra-fuel stability.
--
-- Reuses the same structural-fuel proof discipline as the existing
-- P/NP/FRAC/Karp execution carriers: no recursion on an opaque filter.
--
-- The proof is about the *actual* original Wilson positive-link
-- selector, not arbitrary symbolic machine fuel.
------------------------------------------------------------------------

fuelGreedyOriginalEmpty :
  ∀ {n} (fuel : Nat) →
  fuelGreedyOriginalDisjointStars {n} fuel [] ≡ []
fuelGreedyOriginalEmpty zero = refl
fuelGreedyOriginalEmpty (suc fuel) = refl

fuelGreedyOriginalExtraFuelStable :
  ∀ {n} (fuel extra : Nat)
    (marked : List (Original.Bond n)) →
  Source.length marked ≤ fuel →
  fuelGreedyOriginalDisjointStars (fuel + extra) marked
    ≡ fuelGreedyOriginalDisjointStars fuel marked
fuelGreedyOriginalExtraFuelStable zero extra [] lengthBound =
  fuelGreedyOriginalEmpty extra
fuelGreedyOriginalExtraFuelStable zero extra (a ∷ as) () 
fuelGreedyOriginalExtraFuelStable (suc fuel) extra [] lengthBound = refl
fuelGreedyOriginalExtraFuelStable (suc fuel) extra (a ∷ as)
  lengthBound =
  cong (λ selected → a ∷ selected)
    (fuelGreedyOriginalExtraFuelStable fuel extra
      (Original.filterOriginalStarFree a as)
      (≤-trans
        (filterOriginalStarLengthBound a as)
        (sucBoundInverse lengthBound)))

fuelGreedyOriginalFullLengthExtraFuelStable :
  ∀ {n} (extra : Nat) (marked : List (Original.Bond n)) →
  fuelGreedyOriginalDisjointStars
    (Source.length marked + extra) marked
    ≡ fuelGreedyOriginalDisjointStars
      (Source.length marked) marked
fuelGreedyOriginalFullLengthExtraFuelStable extra marked =
  fuelGreedyOriginalExtraFuelStable
    (Source.length marked) extra marked ≤-refl
