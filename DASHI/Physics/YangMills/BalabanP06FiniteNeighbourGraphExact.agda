module DASHI.Physics.YangMills.BalabanP06FiniteNeighbourGraphExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel, "Graph Theory", Graduate Texts in Mathematics 173,
-- fifth edition, Springer, 2017.
-- DOI: 10.1007/978-3-662-53622-3.
--
-- PURPOSE
-- Provide a concrete sibling to the legacy Graph.countNeighbors socket.  A
-- finite-neighbour graph owns its neighbour enumeration and degree function by
-- definition; the periodic four-dimensional instance therefore has degree at
-- most eight without any abstract counting identification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _≤_)

import DASHI.Physics.YangMills.GraphCombinatorics as Graph
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as WordEntropy
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPhysicalAdjacencyAndBadReachExact as Physical
import DASHI.Physics.YangMills.BalabanP06PeriodicSupportDegreeExact as PeriodicDegree
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact using (eight)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record FiniteNeighbourGraph : Set₁ where
  field
    Vertex : Set
    Edge : Set
    Adjacent : Vertex → Vertex → Set
    Member : Vertex → List Vertex → Set
    neighbours : Vertex → List Vertex
    everyAdjacentEnumerated : ∀ {left right} →
      Adjacent left right →
      Member right (neighbours left)

open FiniteNeighbourGraph public

underlyingGraph : FiniteNeighbourGraph → Graph.Graph
underlyingGraph finite = record
  { Graph.Graph.Vertex = Vertex finite
  ; Graph.Graph.Edge = Edge finite
  ; Graph.Graph.Adj = Adjacent finite
  }

concreteDegree :
  (finite : FiniteNeighbourGraph) → Vertex finite → Nat
concreteDegree finite vertex =
  Graph.countUnique (neighbours finite vertex)

ConcreteBoundedDegree : FiniteNeighbourGraph → Nat → Set
ConcreteBoundedDegree finite bound =
  ∀ vertex → concreteDegree finite vertex ≤ bound

periodicFiniteNeighbourGraph : Nat → FiniteNeighbourGraph
periodicFiniteNeighbourGraph n = record
  { Vertex = Periodic.PeriodicBlock n
  ; Edge = WordEntropy.SignedAxis4
  ; Adjacent = Physical.PeriodicPhysicalAdjacent
  ; Member = Carrier._∈_
  ; neighbours = PeriodicDegree.periodicNeighbourEnumeration
  ; everyAdjacentEnumerated =
      PeriodicDegree.physicalNeighbourEnumerated
  }

periodicConcreteDegreeDefinition :
  ∀ {n} block →
  concreteDegree (periodicFiniteNeighbourGraph n) block
  ≡ PeriodicDegree.periodicDistinctNeighbourCount block
periodicConcreteDegreeDefinition block = refl

periodicConcreteBoundedDegreeEight :
  ∀ n → ConcreteBoundedDegree (periodicFiniteNeighbourGraph n) eight
periodicConcreteBoundedDegreeEight n block =
  PeriodicDegree.periodicDistinctNeighbourCountBelowEight block

record LegacyCountNeighboursCompatibility
    (finite : FiniteNeighbourGraph) : Set₁ where
  field
    legacyCountEqualsConcrete : ∀ vertex →
      Graph.countNeighbors (underlyingGraph finite) vertex
      ≡ concreteDegree finite vertex

open LegacyCountNeighboursCompatibility public

legacyBoundedDegreeFromConcrete :
  ∀ {finite bound} →
  LegacyCountNeighboursCompatibility finite →
  ConcreteBoundedDegree finite bound →
  Graph.BoundedDegree (underlyingGraph finite) bound
legacyBoundedDegreeFromConcrete compatibility bounded vertex
  rewrite legacyCountEqualsConcrete compatibility vertex =
  bounded vertex

finiteNeighbourGraphDefinitionLevel : ProofLevel
finiteNeighbourGraphDefinitionLevel = machineChecked

periodicConcreteDegreeEightLevel : ProofLevel
periodicConcreteDegreeEightLevel = machineChecked

legacyCountNeighboursCompatibilityLevel : ProofLevel
legacyCountNeighboursCompatibilityLevel = conditional
