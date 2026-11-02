module DASHI.Mathematics.Complexity.Karp21FiniteNodeSetCoverDecisionExact where

------------------------------------------------------------------------
-- Historical E06, Richard M. Karp (1972): NODE COVER -> SET COVERING.
-- Existing DASHI owner Karp21VertexSetCoverIncidenceExact proves
-- pointwise vertex↔incidence-set cover. This module upgrades that
-- theorem to the SAME FINITE n-VERTEX GRAPH and a true existential
-- decision predicate with cardinality at most k.
--
-- For each source vertex, the target subset consists of exactly the
-- edges incident to that vertex. This is the semantic finite set-system
-- abstraction; target packed bitsets, malformed graph words, exact
-- universe coverage and machine polynomial clock remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _×_; _,_)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Graph
import DASHI.Mathematics.Complexity.Karp21VertexSetCoverIncidenceExact as Incidence
import DASHI.Mathematics.Complexity.Karp21SimpleGraphComplementExact as Simple
import DASHI.Mathematics.Complexity.Karp21FiniteCliqueVertexCoverCombinedExact as Finite

FiniteNodeCoverAt :
  ∀ {n} → Simple.SimpleGraph n → Vec.Vec Bool n → Nat → Set
FiniteNodeCoverAt graph choices budget =
  Graph.VertexCover (Simple.adjacency graph)
    (Finite.selected choices)
  × (Finite.selectedCount choices ≤ budget)

FiniteIncidentSetCoverAt :
  ∀ {n} → Simple.SimpleGraph n → Vec.Vec Bool n → Nat → Set
FiniteIncidentSetCoverAt graph choices budget =
  Incidence.IndexedEdgeSetCover (Simple.adjacency graph)
    (Finite.selected choices)
  × (Finite.selectedCount choices ≤ budget)

nodeCoverToFiniteSetCover :
  ∀ {n} (graph : Simple.SimpleGraph n)
    (choices : Vec.Vec Bool n) (budget : Nat) →
  FiniteNodeCoverAt graph choices budget →
  FiniteIncidentSetCoverAt graph choices budget
nodeCoverToFiniteSetCover graph choices budget (cover , within) =
  Incidence.vertexCoverToIndexedSetCover
    (Simple.adjacency graph)
    (Finite.selected choices)
    cover ,
  within

finiteSetCoverToNodeCover :
  ∀ {n} (graph : Simple.SimpleGraph n)
    (choices : Vec.Vec Bool n) (budget : Nat) →
  FiniteIncidentSetCoverAt graph choices budget →
  FiniteNodeCoverAt graph choices budget
finiteSetCoverToNodeCover graph choices budget (cover , within) =
  Incidence.indexedSetCoverToVertexCover
    (Simple.adjacency graph)
    (Finite.selected choices)
    cover ,
  within

FiniteNodeCoverYES :
  ∀ {n} → Simple.SimpleGraph n → Nat → Set
FiniteNodeCoverYES {n} graph budget =
  Σ (Vec.Vec Bool n) (λ choices →
    FiniteNodeCoverAt graph choices budget)

FiniteIncidentSetCoverYES :
  ∀ {n} → Simple.SimpleGraph n → Nat → Set
FiniteIncidentSetCoverYES {n} graph budget =
  Σ (Vec.Vec Bool n) (λ choices →
    FiniteIncidentSetCoverAt graph choices budget)

karpFiniteNodeSetCoverInstanceIff :
  ∀ {n} (graph : Simple.SimpleGraph n) (budget : Nat) →
  PR.Iff
    (FiniteNodeCoverYES graph budget)
    (FiniteIncidentSetCoverYES graph budget)
karpFiniteNodeSetCoverInstanceIff graph budget =
  PR.iff
    (λ { (choices , witness) →
      choices , nodeCoverToFiniteSetCover graph choices budget witness })
    (λ { (choices , witness) →
      choices , finiteSetCoverToNodeCover graph choices budget witness })
