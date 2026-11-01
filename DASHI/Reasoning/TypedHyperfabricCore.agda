module DASHI.Reasoning.TypedHyperfabricCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source calibration: Iulia Duta, Giulia Cassarà, Fabrizio Silvestri and
-- Pietro Liò, "Sheaf Hypergraph Networks", arXiv:2309.17116,
-- DOI 10.48550/arXiv.2309.17116.
--
-- This module imports only the general node/hyperedge stalk and restriction
-- pattern.  It does not import the paper's linear algebra, learning claims or
-- benchmark results.
------------------------------------------------------------------------

record TypedHyperfabric (Vertex Edge : Set) : Set₁ where
  field
    vertexStalk : Vertex → Set
    edgeStalk : Edge → Set
    incidence : Vertex → Edge → Set
    restrict :
      ∀ {vertex edge} →
      incidence vertex edge →
      vertexStalk vertex →
      edgeStalk edge
    edgeProvenance : Edge → List String
    edgeSalience : Edge → Nat
    fabricLabel : String

open TypedHyperfabric public

record GlobalSection
    {Vertex Edge : Set}
    (fabric : TypedHyperfabric Vertex Edge) : Set₁ where
  field
    vertexValue : (vertex : Vertex) → vertexStalk fabric vertex
    edgeValue : (edge : Edge) → edgeStalk fabric edge
    compatible :
      ∀ {vertex edge}
        (membership : incidence fabric vertex edge) →
      restrict fabric membership (vertexValue vertex)
      ≡ edgeValue edge
    sectionReceipt : String

open GlobalSection public

record HyperfabricObstruction
    {Vertex Edge Residual : Set}
    (fabric : TypedHyperfabric Vertex Edge) : Set where
  field
    obstructedEdge : Edge
    residual : Residual
    obstructionProvenance : List String
    obstructionReceipt : String

open HyperfabricObstruction public

record HyperfabricTrace (Edge : Set) : Set where
  field
    visitedEdges : List Edge
    traceReceipts : List String
    traceLabel : String

open HyperfabricTrace public

record ProvenancePreservingReorganisation
    {Vertex Edge : Set}
    (before after : TypedHyperfabric Vertex Edge) : Set₁ where
  field
    edgeMap : Edge → Edge
    provenancePreserved :
      ∀ edge →
      edgeProvenance before edge
      ≡ edgeProvenance after (edgeMap edge)
    incidenceMayChange : Bool
    transportMayChange : Bool
    stalkContentErased : Bool
    reorganisationReceipt : String

open ProvenancePreservingReorganisation public

record TypedHyperfabricAuthorityBoundary : Set where
  field
    higherArityRelationsRepresentable : Bool
    localStalksRepresentable : Bool
    restrictionMapsRepresentable : Bool
    globalSectionRequiresCompatibilityWitness : Bool
    hyperfabricEqualsNeuralNetworkClaimed : Bool
    obstructionAutomaticallyDiagnosesPerson : Bool
    sourceCitationImportsEmpiricalPerformance : Bool
    boundaryNote : String

canonicalTypedHyperfabricAuthorityBoundary :
  TypedHyperfabricAuthorityBoundary
canonicalTypedHyperfabricAuthorityBoundary = record
  { higherArityRelationsRepresentable = true
  ; localStalksRepresentable = true
  ; restrictionMapsRepresentable = true
  ; globalSectionRequiresCompatibilityWitness = true
  ; hyperfabricEqualsNeuralNetworkClaimed = false
  ; obstructionAutomaticallyDiagnosesPerson = false
  ; sourceCitationImportsEmpiricalPerformance = false
  ; boundaryNote =
      "The core is a typed sheaf-like hypergraph carrier: local data and incidence transport are explicit, while analytic, learned and clinical claims remain separate."
  }
