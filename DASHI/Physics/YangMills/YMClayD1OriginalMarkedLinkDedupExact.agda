module DASHI.Physics.YangMills.YMClayD1OriginalMarkedLinkDedupExact where

------------------------------------------------------------------------
-- Canonical finite set of ACTUAL source positive Wilson links.
--
-- The 19-packing theorem has a necessary distinct-marked premise.
-- An arbitrary finite marked list may contain duplicate link indices:
-- the 19 bound must apply to distinct source variables, NOT list
-- occurrences. This module constructs that correct canonical carrier
-- with no new axioms and no external model-leaf assumption.
--
-- All source equality decisions are the exact Torus.PositiveBond
-- equality used by the original Wilson plaquette graph.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Properties using (≤-refl)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayD1OriginalPlaquetteSupportDecisionExact as Original
import DASHI.Physics.YangMills.YMClayD1OriginalPeriodicPlaquetteFourBondSupportExact as Source
import DASHI.Physics.YangMills.YMClayD1OriginalGreedy19CountingExact as Count
import DASHI.Physics.YangMills.YMClayD1OriginalFuelGreedyTerminationExact as Fuel

originalDeduplicateLinks :
  ∀ {n} → List (Original.Bond n) → List (Original.Bond n)
originalDeduplicateLinks [] = []
originalDeduplicateLinks (a ∷ as)
  with Original.decideBondIn a (originalDeduplicateLinks as)
... | Torus.yes _ = originalDeduplicateLinks as
... | Torus.no _ = a ∷ originalDeduplicateLinks as

originalDeduplicateLinksDistinct :
  ∀ {n} (marked : List (Original.Bond n)) →
  Count.DistinctMarked (originalDeduplicateLinks marked)
originalDeduplicateLinksDistinct [] = Count.distinctNil
originalDeduplicateLinksDistinct (a ∷ as)
  with Original.decideBondIn a (originalDeduplicateLinks as)
... | Torus.yes _ = originalDeduplicateLinksDistinct as
... | Torus.no absent =
  Count.distinctCons absent (originalDeduplicateLinksDistinct as)

-- An element of the original marked list cannot disappear.
originalDeduplicateLinksComplete :
  ∀ {n} (marked : List (Original.Bond n))
    (b : Original.Bond n) →
  Torus._∈_ b marked →
  Torus._∈_ b (originalDeduplicateLinks marked)
originalDeduplicateLinksComplete [] b ()
originalDeduplicateLinksComplete (a ∷ as) b Torus.here
  with Original.decideBondIn a (originalDeduplicateLinks as)
... | Torus.yes present = present
... | Torus.no _ = Torus.here
originalDeduplicateLinksComplete (a ∷ as) b (Torus.there member)
  with Original.decideBondIn a (originalDeduplicateLinks as)
... | Torus.yes _ = originalDeduplicateLinksComplete as b member
... | Torus.no _ =
  Torus.there (originalDeduplicateLinksComplete as b member)

-- The canonical list has no invented link variable.
originalDeduplicateLinksSound :
  ∀ {n} (marked : List (Original.Bond n))
    (b : Original.Bond n) →
  Torus._∈_ b (originalDeduplicateLinks marked) →
  Torus._∈_ b marked
originalDeduplicateLinksSound [] b ()
originalDeduplicateLinksSound (a ∷ as) b member
  with Original.decideBondIn a (originalDeduplicateLinks as)
... | Torus.yes _ =
  Torus.there (originalDeduplicateLinksSound as b member)
... | Torus.no _ with member
...   | Torus.here = Torus.here
...   | Torus.there inTail =
  Torus.there (originalDeduplicateLinksSound as b inTail)

-- Application-ready true original-link selector, no distinctness
-- obligation on the original input (duplicates are normalized).
originalCanonicalGreedySelection :
  ∀ {n} → List (Original.Bond n) → List (Original.Bond n)
originalCanonicalGreedySelection marked =
  Fuel.fuelGreedyOriginalDisjointStars
    (Source.length (originalDeduplicateLinks marked))
    (originalDeduplicateLinks marked)

originalCanonicalGreedyIsIndependent :
  ∀ {n} (marked : List (Original.Bond n)) →
  Original.AllOriginalStarsIndependent
    (originalCanonicalGreedySelection marked)
originalCanonicalGreedyIsIndependent marked =
  Fuel.fuelGreedyOriginalIndependent
    (Source.length (originalDeduplicateLinks marked))
    (originalDeduplicateLinks marked)

originalCanonicalGreedySubset :
  ∀ {n} (marked : List (Original.Bond n))
    (b : Original.Bond n) →
  Torus._∈_ b (originalCanonicalGreedySelection marked) →
  Torus._∈_ b marked
originalCanonicalGreedySubset marked b selected =
  originalDeduplicateLinksSound marked b
    (Fuel.fuelGreedyOriginalSubset
      (Source.length (originalDeduplicateLinks marked))
      (originalDeduplicateLinks marked) b selected)

originalCanonicalGreedyMaximal :
  ∀ {n} (marked : List (Original.Bond n))
    (b : Original.Bond n) →
  Torus._∈_ b marked →
  Original.OriginalStarDominated b
    (originalCanonicalGreedySelection marked)
originalCanonicalGreedyMaximal marked b selected =
  Fuel.fuelGreedyWithFullLengthIsMaximal
    (originalDeduplicateLinks marked) b
    (originalDeduplicateLinksComplete marked b selected)

-- Quantitative result for the correct set cardinality, now usable on
-- ANY original marked list. OriginalStar18RemovalBound remains an
-- uninhabited physical-geometry obligation, not an assumption hidden
-- in this implementation.
originalCanonical19Packing :
  (degree : Count.OriginalStar18RemovalBound) →
  ∀ {n} (marked : List (Original.Bond n)) →
  Source.length (originalDeduplicateLinks marked) ≤
    Count.nineteenTimes
      (Source.length (originalCanonicalGreedySelection marked))
originalCanonical19Packing degree marked =
  Fuel.fuelGreedyOriginal19PackingFullLength
    degree (originalDeduplicateLinks marked)
    (originalDeduplicateLinksDistinct marked)
