module DASHI.Physics.YangMills.BalabanP06PeriodicSupportBridgeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel,
-- "Graph Theory", Graduate Texts in Mathematics 173, fifth edition,
-- Springer, 2017. DOI: 10.1007/978-3-662-53622-3.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Instantiate the lightweight P06 support carrier with the repository's
-- literal periodic four-dimensional block graph.  The graph, neighbour
-- enumeration, root and degree-eight theorem are no longer abstract inputs.
-- Only the semantic list predicates and their physical adjacency equivalence
-- remain as an explicit bridge record.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanP06FiniteNeighbourGraphExact as FiniteGraph
import DASHI.Physics.YangMills.BalabanP06PhysicalModelLeafLightweightExact as P06
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as WordEntropy
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PeriodicSupportSemantics (n : Nat) : Set₁ where
  field
    Member :
      Periodic.PeriodicBlock n →
      List (Periodic.PeriodicBlock n) → Set

    NoDuplicates :
      List (Periodic.PeriodicBlock n) → Set

    Connected :
      List (Periodic.PeriodicBlock n) → Set

    PhysicalAdjacent :
      Periodic.PeriodicBlock n →
      Periodic.PeriodicBlock n → Set

    leastBlockBelongs : ∀ polymer →
      Member (Periodic.leastBlockList polymer) polymer

    polymerNoDuplicates : ∀ polymer →
      NoDuplicates polymer

    polymerConnected : ∀ polymer →
      Connected polymer

    graphAdjacencyIsPhysical : ∀ {left right} →
      FiniteGraph.Adjacent
        (FiniteGraph.periodicFiniteNeighbourGraph n)
        left right →
      PhysicalAdjacent left right

    physicalAdjacencyIsGraph : ∀ {left right} →
      PhysicalAdjacent left right →
      FiniteGraph.Adjacent
        (FiniteGraph.periodicFiniteNeighbourGraph n)
        left right

open PeriodicSupportSemantics public

periodicPhysicalPolymerSupportModel :
  ∀ n →
  PeriodicSupportSemantics n →
  P06.PhysicalPolymerSupportModel
periodicPhysicalPolymerSupportModel n semantics = record
  { graph = FiniteGraph.periodicFiniteNeighbourGraph n
  ; Polymer = Periodic.PeriodicPolymer n
  ; support = λ polymer → polymer
  ; root = Periodic.leastBlockList
  ; Member = Member semantics
  ; NoDuplicates = NoDuplicates semantics
  ; Connected = Connected semantics
  ; PhysicalAdjacent = PhysicalAdjacent semantics
  ; rootBelongsToSupport = leastBlockBelongs semantics
  ; supportHasNoDuplicates = polymerNoDuplicates semantics
  ; supportIsConnected = polymerConnected semantics
  ; supportAdjacencyForward = graphAdjacencyIsPhysical semantics
  ; supportAdjacencyBackward = physicalAdjacencyIsGraph semantics
  ; concreteDegreeBound = WordEntropy.eight
  ; concreteDegreeUniform =
      FiniteGraph.periodicConcreteBoundedDegreeEight n
  }

periodicSupportGraphDefinitionLevel : ProofLevel
periodicSupportGraphDefinitionLevel = machineChecked

periodicSupportRootDefinitionLevel : ProofLevel
periodicSupportRootDefinitionLevel = machineChecked

periodicSupportDegreeEightLevel : ProofLevel
periodicSupportDegreeEightLevel = machineChecked

periodicSupportSemanticBridgeLevel : ProofLevel
periodicSupportSemanticBridgeLevel = conditional
