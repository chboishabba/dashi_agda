{-# OPTIONS --safe #-}
module DASHI.Reasoning.TrialecticDirectedSourceTargetHyperfabricExact where

------------------------------------------------------------------------
-- SOURCE-TARGET TYPED HYPERFABRIC FOR EXACT THREE-NODE DIRECTED MATRIX.
--
-- Reuses TypedHyperfabricCore's EXISTING stalk/incidence/restrict/
-- GlobalSection.  Every arrow (s -> t) has two *role-indexed*
-- incidence witnesses:
--
--   atSource s (s -> t) : outgoing(s)[t]
--   atTarget t (s -> t) : incoming(t)[s]
--
-- Both restrictions equal the SAME oriented edge weight w(s,t).
-- This DOES NOT assert w(s,t) = w(t,s).  A loop carries both
-- source and target roles at its single vertex.
--
-- Source: standard directed weighted graph / matrix correspondence.
-- ICLR 2026 Fiorini et al., "Sheaves Reloaded: A Direction Awakening",
-- and Mule et al., "Directional Sheaf Hypergraph Networks", provide
-- conceptual directionality context only.  No Laplacian, neural-network
-- benchmark, analytical sheaf, or smooth pants construction imported.
-- Formal finite adapter and proof ownership: DASHI.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Reasoning.TypedHyperfabricCore as Fabric
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.TrialecticWeightedDirectedGraph369Exact as Graph

data DirectedEdge : Set where
  directed-edge : Observer.Participant3 -> Observer.Participant3 -> DirectedEdge

record DirectedVertexRow : Set where
  constructor directed-vertex-row
  field
    outgoing : Observer.Participant3 -> Nat
    incoming : Observer.Participant3 -> Nat
open DirectedVertexRow public

data DirectedIncidence : Observer.Participant3 -> DirectedEdge -> Set where
  atSource :
    ∀ {source target} ->
    DirectedIncidence source (directed-edge source target)
  atTarget :
    ∀ {source target} ->
    DirectedIncidence target (directed-edge source target)

restrictDirected :
  ∀ {vertex edge} ->
  DirectedIncidence vertex edge ->
  DirectedVertexRow ->
  Nat
restrictDirected (atSource {target = target}) row = outgoing row target
restrictDirected (atTarget {source = source}) row = incoming row source

directedWeightFabric :
  Fabric.TypedHyperfabric Observer.Participant3 DirectedEdge
directedWeightFabric = record
  { vertexStalk = λ _ -> DirectedVertexRow
  ; edgeStalk = λ _ -> Nat
  ; incidence = DirectedIncidence
  ; restrict = restrictDirected
  ; edgeProvenance = λ _ ->
      "source: 26 October 2026 supplied matrix illustration" ∷ []
  ; edgeSalience =
      λ { (directed-edge source target) -> Graph.dankaWeight source target }
  ; fabricLabel = "two-ended directed-weight fabric with source/target roles"
  }

outgoingIncomingRow : Observer.Participant3 -> DirectedVertexRow
outgoingIncomingRow vertex =
  directed-vertex-row
    (λ target -> Graph.dankaWeight vertex target)
    (λ source -> Graph.dankaWeight source vertex)

directedWeightSection : Fabric.GlobalSection directedWeightFabric
directedWeightSection = record
  { vertexValue = outgoingIncomingRow
  ; edgeValue =
      λ { (directed-edge source target) -> Graph.dankaWeight source target }
  ; compatible = λ { (atSource {source = source} {target = target}) -> refl
                   ; (atTarget {source = source} {target = target}) -> refl }
  ; sectionReceipt =
      "source outgoing and target incoming restrictions agree per oriented arrow"
  }

-- The same A->B arrow has separately accessible source and target
-- restrictions, both with weight 10 tenths.
sourceAtoBWeight :
  restrictDirected
    (atSource
      {source = Observer.participantA}
      {target = Observer.participantB})
    (outgoingIncomingRow Observer.participantA)
  ≡ 10
sourceAtoBWeight = refl

targetAtoBWeight :
  restrictDirected
    (atTarget
      {source = Observer.participantA}
      {target = Observer.participantB})
    (outgoingIncomingRow Observer.participantB)
  ≡ 10
targetAtoBWeight = refl

-- The reverse arrow has its own source and target restrictions and
-- weight 2, not 10. Both directed arrows are still globally compatible.
sourceBtoAWeight :
  restrictDirected
    (atSource
      {source = Observer.participantB}
      {target = Observer.participantA})
    (outgoingIncomingRow Observer.participantB)
  ≡ 2
sourceBtoAWeight = refl

targetBtoAWeight :
  restrictDirected
    (atTarget
      {source = Observer.participantB}
      {target = Observer.participantA})
    (outgoingIncomingRow Observer.participantA)
  ≡ 2
targetBtoAWeight = refl

-- A->A loop has two incidence roles at vertex A, each with weight 5.
loopSourceWeight :
  restrictDirected
    (atSource
      {source = Observer.participantA}
      {target = Observer.participantA})
    (outgoingIncomingRow Observer.participantA)
  ≡ 5
loopSourceWeight = refl

loopTargetWeight :
  restrictDirected
    (atTarget
      {source = Observer.participantA}
      {target = Observer.participantA})
    (outgoingIncomingRow Observer.participantA)
  ≡ 5
loopTargetWeight = refl

forwardBackwardNotSymmetric :
  Graph.dankaWeight Observer.participantA Observer.participantB
  ≡ Graph.dankaWeight Observer.participantB Observer.participantA -> ⊥
forwardBackwardNotSymmetric =
  Graph.reverseEdgeDoesNotPreserveWeight

record DirectedFabricBoundary : Set where
  constructor directed-fabric-boundary
  field
    sourceAndTargetRestrictionExplicit : Bool
    globalSectionCompatibleBothRoles : Bool
    reversedEdgeWeightMayDiffer : Bool
    twoRolesForOneLoop : Bool
    independentTriadicFaceReconstructed : Bool
    smoothPantsOrDirectedLaplacianClaimed : Bool
    2026PaperCreatesKernelAuthority : Bool
    exactHeadKernelChecked : Bool

canonicalDirectedFabricBoundary : DirectedFabricBoundary
canonicalDirectedFabricBoundary =
  directed-fabric-boundary
    true true true true false false false false
