module DASHI.Physics.YangMills.BalabanP06PeriodicGraphAdapterExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel, "Graph Theory", Graduate Texts in Mathematics 173,
-- 5th edition, Springer, 2017. DOI: 10.1007/978-3-662-53622-3.
--
-- PURPOSE
--
-- Build the literal GraphCombinatorics graph for periodic four-dimensional
-- block adjacency.  The physical eight-direction degree estimate is already
-- proved in BalabanP06PeriodicSupportDegreeExact.  Because the legacy generic
-- graph layer keeps `countNeighbors` as an abstract compatibility socket, the
-- only remaining field is the equality identifying that socket with the
-- concrete duplicate-free neighbour count.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4; eight)
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPhysicalAdjacencyAndBadReachExact as Physical
import DASHI.Physics.YangMills.BalabanP06PeriodicSupportDegreeExact as Degree
import DASHI.Physics.YangMills.GraphCombinatorics as Graph
open import DASHI.Physics.YangMills.CompactLieProofLevel

periodicSupportGraph : Nat → Graph.Graph
periodicSupportGraph n = record
  { Vertex = Periodic.PeriodicBlock n
  ; Edge = SignedAxis4
  ; Adj = Physical.PeriodicPhysicalAdjacent
  }

record PeriodicCountNeighborsIdentification (n : Nat) : Set₁ where
  field
    countNeighborsMatchesConcrete :
      ∀ block →
      Graph.countNeighbors (periodicSupportGraph n) block
        ≡ Degree.periodicDistinctNeighbourCount block

open PeriodicCountNeighborsIdentification public

periodicSupportGraphBoundedDegreeEight :
  ∀ {n} →
  PeriodicCountNeighborsIdentification n →
  Graph.BoundedDegree (periodicSupportGraph n) eight
periodicSupportGraphBoundedDegreeEight identification block =
  subst
    (λ count → count ≤ eight)
    (sym (countNeighborsMatchesConcrete identification block))
    (Degree.periodicDistinctNeighbourCountBelowEight block)

record PeriodicSupportGraphCertificate (n : Nat) : Set₁ where
  field
    graph : Graph.Graph
    graphIsLiteral : graph ≡ periodicSupportGraph n
    degreeIdentification : PeriodicCountNeighborsIdentification n
    boundedDegreeEight : Graph.BoundedDegree graph eight

open PeriodicSupportGraphCertificate public

periodicSupportGraphCertificate :
  ∀ {n} →
  PeriodicCountNeighborsIdentification n →
  PeriodicSupportGraphCertificate n
periodicSupportGraphCertificate {n} identification = record
  { graph = periodicSupportGraph n
  ; graphIsLiteral = refl
  ; degreeIdentification = identification
  ; boundedDegreeEight =
      periodicSupportGraphBoundedDegreeEight identification
  }

periodicSupportGraphDefinitionLevel : ProofLevel
periodicSupportGraphDefinitionLevel = machineChecked

periodicSupportGraphDegreeReducerLevel : ProofLevel
periodicSupportGraphDegreeReducerLevel = machineChecked

legacyCountNeighborsIdentificationLevel : ProofLevel
legacyCountNeighborsIdentificationLevel = conditional
