module DASHI.Physics.YangMills.YMClayD1OriginalLinkStarFiniteNeighbourGraphExact where

------------------------------------------------------------------------
-- Original Wilson link/plaquette-star conflict graph as a CONCRETE
-- finite-neighbour graph (the existing P06 graph interface).
--
-- Vertices are exact original 4D positive link variables. Adjacency
-- is non-disjoint ORIGINAL incident plaquette stars, NOT block nearest
-- neighbours or positive-link endpoint adjacency. The enumeration is
-- complete and the filter's output is sound. The analytic Gibbs
-- distribution, degree-18 cardinality and polymer activity are separate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClayD1OriginalPlaquetteSupportDecisionExact as Original
import DASHI.Physics.YangMills.BalabanP06FiniteNeighbourGraphExact as P06
import DASHI.Physics.YangMills.YMClayD1OriginalConflictPlaquetteWitnessExact as Witness

-- A complete literal positive-bond enumeration from the SAME fourfold
-- periodic carrier as the original finite Wilson lattice action.
originalAllPositiveLinks :
  (n : Nat) → List (Original.Bond n)
originalAllPositiveLinks n =
  Torus.cartesian
    (Torus.elements (Torus.periodicTorus4Finite (suc n)))
    (Torus.allCyclicIndices Torus.four)

originalAllPositiveLinksComplete :
  ∀ {n} (bond : Original.Bond n) →
  Torus._∈_ bond (originalAllPositiveLinks n)
originalAllPositiveLinksComplete {n} (Torus.pair site axis) =
  Torus.cartesianMembership
    (Torus.complete (Torus.periodicTorus4Finite (suc n)) site)
    (Torus.allCyclicIndicesComplete axis)

-- Unlike generic graph 'Adj', this is the proof-relevant failure of
-- separation in the SAME original incident plaquette lists.
OriginalLinkStarConflict :
  ∀ {n} → Original.Bond n → Original.Bond n → Set
OriginalLinkStarConflict a b =
  Original.OriginalStarsDisjoint a b → Torus.Empty

originalLinkStarConflictDec :
  ∀ {n} (a b : Original.Bond n) →
  Torus.Dec (OriginalLinkStarConflict a b)
originalLinkStarConflictDec a b
  with Original.decideOriginalStarsDisjoint a b
... | Torus.yes separate =
  Torus.no (λ conflict → conflict separate)
... | Torus.no conflict = Torus.yes conflict

-- Select every actual original link with overlapping original plaquettes.
originalConflictingFilter :
  ∀ {n} (a : Original.Bond n) →
  List (Original.Bond n) → List (Original.Bond n)
originalConflictingFilter a [] = []
originalConflictingFilter a (b ∷ bs)
  with originalLinkStarConflictDec a b
... | Torus.yes _ = b ∷ originalConflictingFilter a bs
... | Torus.no _ = originalConflictingFilter a bs

originalConflictingFilterSound :
  ∀ {n} (a : Original.Bond n)
    (bs : List (Original.Bond n)) (b : Original.Bond n) →
  Torus._∈_ b (originalConflictingFilter a bs) →
  OriginalLinkStarConflict a b
originalConflictingFilterSound a [] b ()
originalConflictingFilterSound a (head ∷ bs) b membership
  with originalLinkStarConflictDec a head
... | Torus.yes conflict with membership
...   | Torus.here = conflict
...   | Torus.there inTail =
  originalConflictingFilterSound a bs b inTail
... | Torus.no _ = originalConflictingFilterSound a bs b membership

originalConflictingFilterComplete :
  ∀ {n} (a : Original.Bond n)
    (bs : List (Original.Bond n)) (b : Original.Bond n) →
  Torus._∈_ b bs →
  OriginalLinkStarConflict a b →
  Torus._∈_ b (originalConflictingFilter a bs)
originalConflictingFilterComplete a [] b () conflicting
originalConflictingFilterComplete a (head ∷ bs) b
  Torus.here conflicting with originalLinkStarConflictDec a head
... | Torus.yes _ = Torus.here
... | Torus.no absent = Original.emptyElim (absent conflicting)
originalConflictingFilterComplete a (head ∷ bs) b
  (Torus.there inTail) conflicting
  with originalLinkStarConflictDec a head
... | Torus.yes _ =
  Torus.there (originalConflictingFilterComplete a bs b inTail conflicting)
... | Torus.no _ =
  originalConflictingFilterComplete a bs b inTail conflicting

originalLinkStarNeighbourList :
  ∀ {n} → Original.Bond n → List (Original.Bond n)
originalLinkStarNeighbourList {n} a =
  originalConflictingFilter a (originalAllPositiveLinks n)

originalNeighbourConflictSound :
  ∀ {n} (a b : Original.Bond n) →
  Torus._∈_ b (originalLinkStarNeighbourList a) →
  OriginalLinkStarConflict a b
originalNeighbourConflictSound {n} a b =
  originalConflictingFilterSound a (originalAllPositiveLinks n) b

originalNeighbourConflictComplete :
  ∀ {n} (a b : Original.Bond n) →
  OriginalLinkStarConflict a b →
  Torus._∈_ b (originalLinkStarNeighbourList a)
originalNeighbourConflictComplete {n} a b conflicting =
  originalConflictingFilterComplete a (originalAllPositiveLinks n) b
    (originalAllPositiveLinksComplete b) conflicting

-- The existing finite-neighbour counting framework now has a real
-- same-source ORIGINAL positive-link/plaquette-star instance.
originalLinkStarFiniteNeighbourGraph : Nat → P06.FiniteNeighbourGraph
originalLinkStarFiniteNeighbourGraph n = record
  { P06.FiniteNeighbourGraph.Vertex = Original.Bond n
  ; P06.FiniteNeighbourGraph.Edge = Plaquette.PeriodicPlaquette n
  ; P06.FiniteNeighbourGraph.Adjacent = OriginalLinkStarConflict
  ; P06.FiniteNeighbourGraph.Member = Torus._∈_
  ; P06.FiniteNeighbourGraph.neighbours = originalLinkStarNeighbourList
  ; P06.FiniteNeighbourGraph.everyAdjacentEnumerated =
      λ {left} {right} conflicting →
        originalNeighbourConflictComplete left right conflicting
  }

originalLinkStarGraphDegree :
  ∀ {n} → Original.Bond n → Nat
originalLinkStarGraphDegree {n} bond =
  P06.concreteDegree (originalLinkStarFiniteNeighbourGraph n) bond

originalLinkStarGraphDegreeIsLiteralCount :
  ∀ {n} (bond : Original.Bond n) →
  originalLinkStarGraphDegree bond ≡
    P06.concreteDegree (originalLinkStarFiniteNeighbourGraph n) bond
originalLinkStarGraphDegreeIsLiteralCount bond = refl

-- P06.ConcreteBoundedDegree ... 19 (including self-conflict) is the
-- next native finite theorem. Excluding the vertex itself yields 18.
-- It is NOT inhabited here. Nor is the original Gibbs/cluster activity.

-- Every enumerated neighbour conflict yields the same ORIGINAL
-- four-positive-bond plaquette witnessing the shared Wilson dependency.
originalNeighbourHasLiteralSharedPlaquette :
  ∀ {n} (a b : Original.Bond n) →
  Torus._∈_ b (originalLinkStarNeighbourList a) →
  Witness.SharedOriginalPlaquette a b
originalNeighbourHasLiteralSharedPlaquette a b member =
  Witness.originalConflictExhibitsSharedPlaquette a b
    (originalNeighbourConflictSound a b member)
