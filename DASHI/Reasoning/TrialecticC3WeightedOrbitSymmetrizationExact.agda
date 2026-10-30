{-# OPTIONS --safe #-}
module DASHI.Reasoning.TrialecticC3WeightedOrbitSymmetrizationExact where

------------------------------------------------------------------------
-- CANONICAL C3 ORBIT SUM OF AN ASYMMETRIC WEIGHTED THREE-VERTEX GRAPH
--
-- An arbitrary weighted directed graph on the existing ternary-labelled
-- vertex set does NOT carry a C3 graph action.  Summing the three rotated
-- matrices creates a NEW exact weighted graph whose weights DO admit
-- the original vertex rotation as an automorphism.
--
-- No division by 3 is used: weights remain nonnegative Nat/tenths.
-- This is orbit symmetrization, NOT an equivalence of the original
-- object, nor a Monster/VOA/Dirac/group-action on a physical field.
--
-- Reuses the canonical weighted graph and existing source+target
-- TypedHyperfabric role/incidence and compatibility owners. DASHI
-- owns this finite exact adapter; C3 group averaging is prior art.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Reasoning.TrialecticWeightedDirectedGraph369Exact as Graph
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.TrialecticDirectedSourceTargetHyperfabricExact as Directed
import DASHI.Reasoning.TypedHyperfabricCore as Fabric

rotate : Observer.Participant3 -> Observer.Participant3
rotate = Graph.rotateVertex

rotateTwice : Observer.Participant3 -> Observer.Participant3
rotateTwice v = rotate (rotate v)

orbitSum : Graph.WeightedDigraph3 -> Graph.WeightedDigraph3
orbitSum w source target =
  (w source target + w (rotate source) (rotate target))
  + w (rotateTwice source) (rotateTwice target)

threeTermCycle : (a b c : Nat) -> (b + c) + a ≡ (a + b) + c
threeTermCycle a b c =
  trans (+-comm (b + c) a) (sym (+-assoc a b c))

orbitSumC3Invariant :
  (w : Graph.WeightedDigraph3) ->
  (source target : Observer.Participant3) ->
  orbitSum w (rotate source) (rotate target) ≡ orbitSum w source target
orbitSumC3Invariant w source target
  rewrite Graph.rotateVertexCubed source
        | Graph.rotateVertexCubed target =
  threeTermCycle
    (w source target)
    (w (rotate source) (rotate target))
    (w (rotateTwice source) (rotateTwice target))

-- The supplied image's NEW C3-equivariant orbit-sum matrix,
-- still using the integer-tenths convention:
--   [ 5 50 22 ]
--   [22  5 50 ]
--   [50 22  5 ]
-- This is not equal to the original asymmetric 3x3 fixture.
equivariantImageWeight : Graph.WeightedDigraph3
equivariantImageWeight = orbitSum Graph.dankaWeight

equivariantImageMatrix :
  Graph.digraphToMatrix equivariantImageWeight
  ≡ Observer.observerMatrix3
      5 50 22
      22 5 50
      50 22 5
equivariantImageMatrix = refl

originalGraphC3StillFails :
  ((source target : Observer.Participant3) ->
    Graph.dankaWeight (rotate source) (rotate target)
    ≡ Graph.dankaWeight source target) -> ⊥
originalGraphC3StillFails = Graph.weightedDankaGraphNotC3Invariant

orbitSumChangesTheGraph :
  equivariantImageWeight Observer.participantA Observer.participantB
  ≡ Graph.dankaWeight Observer.participantA Observer.participantB -> ⊥
orbitSumChangesTheGraph ()

------------------------------------------------------------------------
-- A generic instance of the exact SAME existing oriented source/target
-- hyperfabric role and restriction types. No third-party sheaf operator.
------------------------------------------------------------------------

directedFabricFor :
  (w : Graph.WeightedDigraph3) ->
  Fabric.TypedHyperfabric Observer.Participant3 Directed.DirectedEdge
directedFabricFor w = record
  { vertexStalk = λ _ -> Directed.DirectedVertexRow
  ; edgeStalk = λ _ -> Nat
  ; incidence = Directed.DirectedIncidence
  ; restrict = Directed.restrictDirected
  ; edgeProvenance = λ _ ->
      "synthetic C3 orbit sum, original 2026-10-26 matrix credited separately" ∷ []
  ; edgeSalience =
      λ { (Directed.directed-edge source target) -> w source target }
  ; fabricLabel = "source/target directed fabric with explicit chosen weights"
  }

rowsFor :
  (w : Graph.WeightedDigraph3) ->
  Observer.Participant3 -> Directed.DirectedVertexRow
rowsFor w vertex =
  Directed.directed-vertex-row
    (λ target -> w vertex target)
    (λ source -> w source vertex)

compatibleSectionFor :
  (w : Graph.WeightedDigraph3) ->
  Fabric.GlobalSection (directedFabricFor w)
compatibleSectionFor w = record
  { vertexValue = rowsFor w
  ; edgeValue = λ {
      (Directed.directed-edge source target) -> w source target
      }
  ; compatible = λ {
      (Directed.atSource {source = source} {target = target}) -> refl
    ; (Directed.atTarget {source = source} {target = target}) -> refl
      }
  ; sectionReceipt =
      "both directed incidence roles restrict to the chosen oriented weight"
  }

equivariantDirectedFabric :
  Fabric.TypedHyperfabric Observer.Participant3 Directed.DirectedEdge
equivariantDirectedFabric = directedFabricFor equivariantImageWeight

equivariantDirectedSection :
  Fabric.GlobalSection equivariantDirectedFabric
equivariantDirectedSection = compatibleSectionFor equivariantImageWeight

-- These are the exact pointwise outgoing and incoming transport laws,
-- at the source and target stalks respectively; they DO NOT assert
-- transport of an arbitrary connected sheaf or a source-justified face.
outgoingC3Transport :
  (vertex target : Observer.Participant3) ->
  Directed.outgoing (rowsFor equivariantImageWeight (rotate vertex))
    (rotate target)
  ≡ Directed.outgoing (rowsFor equivariantImageWeight vertex) target
outgoingC3Transport vertex target =
  orbitSumC3Invariant Graph.dankaWeight vertex target

incomingC3Transport :
  (vertex source : Observer.Participant3) ->
  Directed.incoming (rowsFor equivariantImageWeight (rotate vertex))
    (rotate source)
  ≡ Directed.incoming (rowsFor equivariantImageWeight vertex) source
incomingC3Transport vertex source =
  orbitSumC3Invariant Graph.dankaWeight source vertex

record C3OrbitSumBoundary : Set where
  constructor c3-orbit-sum-boundary
  field
    originalWeightedGraphNotInvariant : Bool
    newSymmetrizedWeightedGraphInvariant : Bool
    compatibleTwoEndedFabricInstantiated : Bool
    bothRowsTransportUnderC3 : Bool
    originalAndOrbitSumSameObject : Bool
    selectedTriadicFaceTransportProved : Bool
    originalMonster3BOrPhysicalActionProved : Bool
    exactHeadKernelChecked : Bool

canonicalC3OrbitSumBoundary : C3OrbitSumBoundary
canonicalC3OrbitSumBoundary =
  c3-orbit-sum-boundary true true true true false false false false
