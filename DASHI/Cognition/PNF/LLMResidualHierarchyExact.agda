module DASHI.Cognition.PNF.LLMResidualHierarchyExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- COMPUTATIONAL / SEMANTIC / PROVENANCE RESIDUALS
--
-- KV-like state sufficient for continuation, state sufficient for semantic
-- reopening, and state sufficient for exact provenance reconstruction are
-- distinct obligations.  This finite carrier gives strict witnesses rather
-- than assuming one residual notion serves all three consumers.
------------------------------------------------------------------------

record FineState : Set where
  constructor fineState
  field
    computeCoordinate : Bool
    semanticCoordinate : Bool
    provenanceCoordinate : Bool

open FineState public

ComputeResidual : Set
ComputeResidual = Bool

SemanticResidual : Set
SemanticResidual = Bool × Bool

ProvenanceResidual : Set
ProvenanceResidual = FineState

computeResidual : FineState → ComputeResidual
computeResidual state = computeCoordinate state

semanticResidual : FineState → SemanticResidual
semanticResidual state = computeCoordinate state , semanticCoordinate state

provenanceResidual : FineState → ProvenanceResidual
provenanceResidual state = state

computeCost semanticCost provenanceCost : Nat
computeCost = 1
semanticCost = 2
provenanceCost = 3

computeCostBelowSemantic : computeCost < semanticCost
computeCostBelowSemantic = s≤s (s≤s z≤n)

semanticCostBelowProvenance : semanticCost < provenanceCost
semanticCostBelowProvenance = s≤s (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Strictness witnesses.
------------------------------------------------------------------------

sameComputeDifferentSemanticLeft sameComputeDifferentSemanticRight : FineState
sameComputeDifferentSemanticLeft = fineState false false false
sameComputeDifferentSemanticRight = fineState false true false

computeResidualCollidesAcrossSemanticDifference :
  computeResidual sameComputeDifferentSemanticLeft
  ≡ computeResidual sameComputeDifferentSemanticRight
computeResidualCollidesAcrossSemanticDifference = refl

semanticDifferenceSurvives :
  semanticCoordinate sameComputeDifferentSemanticLeft
  ≡ semanticCoordinate sameComputeDifferentSemanticRight → ⊥
semanticDifferenceSurvives ()

sameSemanticDifferentProvenanceLeft sameSemanticDifferentProvenanceRight : FineState
sameSemanticDifferentProvenanceLeft = fineState true true false
sameSemanticDifferentProvenanceRight = fineState true true true

semanticResidualCollidesAcrossProvenanceDifference :
  semanticResidual sameSemanticDifferentProvenanceLeft
  ≡ semanticResidual sameSemanticDifferentProvenanceRight
semanticResidualCollidesAcrossProvenanceDifference = refl

provenanceDifferenceSurvives :
  provenanceCoordinate sameSemanticDifferentProvenanceLeft
  ≡ provenanceCoordinate sameSemanticDifferentProvenanceRight → ⊥
provenanceDifferenceSurvives ()

------------------------------------------------------------------------
-- Exact provenance reopening.
------------------------------------------------------------------------

reopenProvenance : ProvenanceResidual → FineState
reopenProvenance state = state

provenanceResidualReopensExact :
  (state : FineState) → reopenProvenance (provenanceResidual state) ≡ state
provenanceResidualReopensExact state = refl

------------------------------------------------------------------------
-- The hierarchy is consumer-relative, not metaphysical: an application that
-- needs only continuation may legitimately stop at ComputeResidual, while an
-- audit/review consumer may require the larger provenance residual.
------------------------------------------------------------------------
