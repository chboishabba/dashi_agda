module DASHI.Physics.YangMills.YMClayD1OriginalGreedy19CountingExact where

------------------------------------------------------------------------
-- Finite ORIGINAL Wilson greedy cardinality transport.
-- This closes the list-arithmetic / no-duplicate side of the 19 cut.
-- The independent geometric degree-18 bound is the single explicit
-- remaining input to the quantitative result; it is NOT assumed true
-- of lists containing duplicates, and is NOT a physical Gibbs estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; +-mono-≤)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayD1OriginalPeriodicPlaquetteFourBondSupportExact as Source
import DASHI.Physics.YangMills.YMClayD1OriginalPlaquetteSupportDecisionExact as Original

-- This predicate is on the literal ORIGINAL positive bond carrier.
data DistinctMarked {n} : List (Original.Bond n) → Set where
  distinctNil : DistinctMarked []
  distinctCons :
    ∀ {a as} →
    (Torus._∈_ a as → Torus.Empty) →
    DistinctMarked as →
    DistinctMarked (a ∷ as)

-- Decidable original star filter cannot manufacture duplicates.
filterOriginalStarFreePreservesDistinct :
  ∀ {n} (a : Original.Bond n) (as : List (Original.Bond n)) →
  DistinctMarked as →
  DistinctMarked (Original.filterOriginalStarFree a as)
filterOriginalStarFreePreservesDistinct a [] distinctNil = distinctNil
filterOriginalStarFreePreservesDistinct a (b ∷ bs)
  (distinctCons absent distinctTail)
  with Original.decideOriginalStarsDisjoint a b
... | Torus.yes _ =
  distinctCons
    (λ inFiltered →
      absent (Original.filterOriginalStarFreeSubset a bs inFiltered))
    (filterOriginalStarFreePreservesDistinct a bs distinctTail)
... | Torus.no _ =
  filterOriginalStarFreePreservesDistinct a bs distinctTail

filterOriginalStarFreeKeepsSelectedHeadDistinct :
  ∀ {n} (a : Original.Bond n) (as : List (Original.Bond n)) →
  DistinctMarked (a ∷ as) →
  DistinctMarked (a ∷ Original.filterOriginalStarFree a as)
filterOriginalStarFreeKeepsSelectedHeadDistinct a as
  (distinctCons absent tailDistinct) =
  distinctCons
    (λ inFiltered →
      absent (Original.filterOriginalStarFreeSubset a as inFiltered))
    (filterOriginalStarFreePreservesDistinct a as tailDistinct)

nineteenTimes : Nat → Nat
nineteenTimes zero = zero
nineteenTimes (suc k) = 19 + nineteenTimes k

-- This is precisely the finite geometric counting input:
-- among distinct as, at most 18 links can conflict with chosen a.
-- The native source geometry must PROVE this bound, not fill it in
-- with a postulate or an arbitrary certificate for an empty input.
record OriginalStar18RemovalBound : Set₁ where
  field
    originalDistinctStarRemovalBound :
      ∀ {n} (a : Original.Bond n)
        (as : List (Original.Bond n)) →
      DistinctMarked (a ∷ as) →
      Source.length as ≤
        18 + Source.length (Original.filterOriginalStarFree a as)

open OriginalStar18RemovalBound public

originalGreedy19PackingFromNativeDegree18 :
  (degree : OriginalStar18RemovalBound) →
  ∀ {n} (marked : List (Original.Bond n)) →
  DistinctMarked marked →
  Source.length marked ≤
    nineteenTimes (Source.length (Original.greedyOriginalDisjointStars marked))
originalGreedy19PackingFromNativeDegree18 degree [] distinctNil = z≤n
originalGreedy19PackingFromNativeDegree18 degree (a ∷ as)
  (distinctCons absent tailDistinct) =
  s≤s
    (≤-trans
      (originalDistinctStarRemovalBound degree a as
        (distinctCons absent tailDistinct))
      (+-mono-≤ ≤-refl
        (originalGreedy19PackingFromNativeDegree18 degree
          (Original.filterOriginalStarFree a as)
          (filterOriginalStarFreePreservesDistinct a as tailDistinct))))
