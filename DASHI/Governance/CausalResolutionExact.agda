module DASHI.Governance.CausalResolutionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Causal-resolution order without political truth labels.
--
-- A fine graph is at least as causally resolved as a coarse graph when every
-- fine edge maps to a coarse edge while retaining an explicit source/target
-- representation.  Strict loss is witnessed constructively by two distinct
-- fine edges compressed to the same coarse edge.
------------------------------------------------------------------------

record CausalGraph : Set₁ where
  field
    Node : Set
    Edge : Set
    source : Edge → Node
    target : Edge → Node

open CausalGraph public

record GraphCompression
  (Fine Coarse : CausalGraph) : Set₁ where
  field
    nodeMap : Node Fine → Node Coarse
    edgeMap : Edge Fine → Edge Coarse
    sourceCommutes :
      (e : Edge Fine) →
      nodeMap (source Fine e) ≡ source Coarse (edgeMap e)
    targetCommutes :
      (e : Edge Fine) →
      nodeMap (target Fine e) ≡ target Coarse (edgeMap e)

open GraphCompression public

record EdgeEvidence (G : CausalGraph) : Set₁ where
  field
    Evidence : Set
    supports : Evidence → Edge G → Set

record EvidencePreservingCompression
  (Fine Coarse : CausalGraph)
  (C : GraphCompression Fine Coarse)
  (fineEvidence : EdgeEvidence Fine)
  (coarseEvidence : EdgeEvidence Coarse) : Set₁ where
  field
    evidenceMap :
      EdgeEvidence.Evidence fineEvidence →
      EdgeEvidence.Evidence coarseEvidence

    supportPreserved :
      (w : EdgeEvidence.Evidence fineEvidence) →
      (e : Edge Fine) →
      EdgeEvidence.supports fineEvidence w e →
      EdgeEvidence.supports coarseEvidence
        (evidenceMap w)
        (GraphCompression.edgeMap C e)

------------------------------------------------------------------------
-- Strict causal-resolution loss: distinct mechanisms become one edge.
------------------------------------------------------------------------

record ReificationLoss
  (Fine Coarse : CausalGraph)
  (C : GraphCompression Fine Coarse) : Set₁ where
  field
    leftEdge : Edge Fine
    rightEdge : Edge Fine
    edgesDistinct : leftEdge ≡ rightEdge → ⊥
    compressedTogether :
      GraphCompression.edgeMap C leftEdge
      ≡ GraphCompression.edgeMap C rightEdge

open ReificationLoss public

compressionWithCollisionIsNotInjective :
  ∀ {Fine Coarse : CausalGraph}
  {C : GraphCompression Fine Coarse} →
  ReificationLoss Fine Coarse C →
  ((x y : Edge Fine) →
    GraphCompression.edgeMap C x ≡ GraphCompression.edgeMap C y →
    x ≡ y) →
  ⊥
compressionWithCollisionIsNotInjective loss injective =
  ReificationLoss.edgesDistinct loss
    (injective
      (ReificationLoss.leftEdge loss)
      (ReificationLoss.rightEdge loss)
      (ReificationLoss.compressedTogether loss))

------------------------------------------------------------------------
-- Structural refinement goes the opposite direction: a coarse explanatory
-- edge is decomposed into named fine edges with explicit evidentiary support.
------------------------------------------------------------------------

record StructuralRefinement
  (Coarse Fine : CausalGraph) : Set₁ where
  field
    refine : Edge Coarse → List (Edge Fine)
    inspectable : Edge Fine → Set
    everyRefinedEdgeInspectable :
      (coarse : Edge Coarse) →
      (fine : Edge Fine) →
      Member fine (refine coarse) →
      inspectable fine

------------------------------------------------------------------------
-- Identity of vocabulary does not establish identity of causal graph.
------------------------------------------------------------------------

record CausalResolutionBoundary : Set where
  constructor causalResolutionBoundary
  field
    oneLabelMayReplaceManyMechanisms : Bool
    collisionPreservesInjectiveResolution : Bool
    structuralCritiqueRequiresPoliticalSide : Bool
    inspectableRefinementSupportsResolution : Bool

canonicalCausalResolutionBoundary : CausalResolutionBoundary
canonicalCausalResolutionBoundary =
  causalResolutionBoundary true false false true
