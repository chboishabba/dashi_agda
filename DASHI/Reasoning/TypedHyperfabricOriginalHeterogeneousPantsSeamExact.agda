module DASHI.Reasoning.TypedHyperfabricOriginalHeterogeneousPantsSeamExact where

------------------------------------------------------------------------
-- H2.02: COMPLETE SELECTED ORIGINAL RELATIONAL-PANTS SEAM INSTANCE.
--
-- The source edge stalks are genuinely heterogeneous:
-- outer edge carries the original BoundaryInterface;
-- inner edge carries the original BranchChannel.
--
-- Source-specific realization reconstructs a channel from the
-- outer boundary + original selected-leg witness, and is identity
-- for the inner input channel. The original five-field
-- RelationalBranchCobordismGeometry.outerInnerMatch pays the seam.
--
-- A real two-incidence before-fabric is reorganized into one
-- shared edge with the ORIGINAL five matched observables,
-- while BOTH original provenance lists remain recoverable in
-- the merged edge provenance. This closes the selected finite
-- H2.02 heterogeneous relational-pants specimen only, not an
-- unsupported world-model or all-hyperfabrics claim.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Reasoning.TypedHyperfabricCore as Fabric
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as Gluing
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Seam
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants

-- Original actual vertex/edge and incidence carriers, not an
-- invented zero-incidence example.
Vertex : Set
Vertex = Seam.SeamSide

Edge : Set
Edge = Seam.BeforeSeamEdge

data OuterOriginalBoundary : Set where
  selectedOriginalBoundary : OuterOriginalBoundary

-- Two unequal original source edge stalk types.
OriginalHeterogeneousEdgeStalk : Edge → Set
OriginalHeterogeneousEdgeStalk Seam.outerEdge = Pants.BoundaryInterface
OriginalHeterogeneousEdgeStalk Seam.innerEdge = Pants.BranchChannel

sourceVertexChannel : Vertex → Pants.BranchChannel
sourceVertexChannel Seam.outerSide = Pants.selectedChannel2
sourceVertexChannel Seam.innerSide = Pants.innerInputChannel2

sourceBoundaryOrChannel :
  (edge : Edge) → OriginalHeterogeneousEdgeStalk edge
sourceBoundaryOrChannel Seam.outerEdge = Pants.selectedBoundary2
sourceBoundaryOrChannel Seam.innerEdge = Pants.innerInputChannel2

-- Actual donor-backed realization of a bare boundary into a
-- channel: its other fields come from THE original selected leg.
realizeOriginalBoundary : Pants.BoundaryInterface → Pants.BranchChannel
realizeOriginalBoundary boundary =
  Pants.branchChannel
    boundary
    (Pants.channelWave Pants.selectedChannel2)
    (Pants.destinationBasin Pants.selectedChannel2)
    (Pants.channelReceipt Pants.selectedChannel2)

realizeSourceEdge :
  (edge : Edge) →
  OriginalHeterogeneousEdgeStalk edge →
  Pants.BranchChannel
realizeSourceEdge Seam.outerEdge boundary = realizeOriginalBoundary boundary
realizeSourceEdge Seam.innerEdge channel = channel

-- Selected actual original boundary and full selected channel
-- realize to the same donor channel, without a field-level
-- agreement added as a postulate.
originalOuterRealization :
  realizeSourceEdge Seam.outerEdge Pants.selectedBoundary2
  ≡ Pants.selectedChannel2
originalOuterRealization = refl

originalInnerRealization :
  realizeSourceEdge Seam.innerEdge Pants.innerInputChannel2
  ≡ Pants.innerInputChannel2
originalInnerRealization = refl

heterogeneousBeforeFabric : Fabric.TypedHyperfabric Vertex Edge
heterogeneousBeforeFabric = record
  { vertexStalk = λ _ → Pants.BranchChannel
  ; edgeStalk = OriginalHeterogeneousEdgeStalk
  ; incidence = Seam.BeforeIncidence
  ; restrict = λ
      { Seam.outerMembership channel → Pants.channelBoundary channel
      ; Seam.innerMembership channel → channel
      }
  ; edgeProvenance = λ
      { Seam.outerEdge →
          "source: selectedBoundary2 / selectedChannel2" ∷ []
      ; Seam.innerEdge →
          "source: innerInputChannel2" ∷ []
      }
  ; edgeSalience = λ _ → 1
  ; fabricLabel = "original heterogeneous boundary/channel pants seam"
  }

heterogeneousBeforeSection :
  Fabric.GlobalSection heterogeneousBeforeFabric
heterogeneousBeforeSection = record
  { vertexValue = sourceVertexChannel
  ; edgeValue = sourceBoundaryOrChannel
  ; compatible = λ
      { Seam.outerMembership → refl
      ; Seam.innerMembership → refl
      }
  ; sectionReceipt =
      "selected source boundary and inner channel with actual incidence"
  }

-- An inhabited original HyperfabricPantsGluing over the
-- heterogeneous edge stalks and actual compatible section.
selectedHeterogeneousPantsGluing :
  Gluing.HyperfabricPantsGluing heterogeneousBeforeSection
selectedHeterogeneousPantsGluing =
  Gluing.hyperfabric-pants-gluing
    Seam.outerEdge
    Seam.innerEdge
    realizeSourceEdge
    Pants.outerInnerMatch
    "original full five-field match, with heterogeneous source stalks"

originalHeterogeneousInterfaceIsDonor :
  Gluing.seamInterface selectedHeterogeneousPantsGluing
  ≡ Pants.outerInnerMatch
originalHeterogeneousInterfaceIsDonor = refl

sourceRealizedEdgesMatch :
  Seam.boundarySignature
    (realizeSourceEdge Seam.outerEdge
      (Fabric.edgeValue heterogeneousBeforeSection Seam.outerEdge))
  ≡
  Seam.boundarySignature
    (realizeSourceEdge Seam.innerEdge
      (Fabric.edgeValue heterogeneousBeforeSection Seam.innerEdge))
sourceRealizedEdgesMatch =
  Seam.interfaceMatchImpliesSignatureEquality
    (Gluing.seamInterface selectedHeterogeneousPantsGluing)

-- The merged edge retains all matched source OBSERVABLES,
-- and both source provenance lists in order.
heterogeneousMergedFabric :
  Fabric.TypedHyperfabric Vertex Seam.AfterSeamEdge
heterogeneousMergedFabric = record
  { vertexStalk = λ _ → Pants.BranchChannel
  ; edgeStalk = λ _ → Seam.SeamSignature
  ; incidence = Seam.AfterIncidence
  ; restrict = λ
      { Seam.outerMergedMembership channel →
          Seam.boundarySignature channel
      ; Seam.innerMergedMembership channel →
          Seam.boundarySignature channel
      }
  ; edgeProvenance = λ
      { Seam.mergedSeam →
          Fabric.edgeProvenance heterogeneousBeforeFabric Seam.outerEdge
          ++
          Fabric.edgeProvenance heterogeneousBeforeFabric Seam.innerEdge
      }
  ; edgeSalience = λ _ → 1
  ; fabricLabel = "original heterogeneous pants merged seam"
  }

heterogeneousMergedSection :
  Fabric.GlobalSection heterogeneousMergedFabric
heterogeneousMergedSection = record
  { vertexValue = sourceVertexChannel
  ; edgeValue = λ _ → Seam.boundarySignature Pants.selectedChannel2
  ; compatible = λ
      { Seam.outerMergedMembership → refl
      ; Seam.innerMergedMembership →
          sym (Seam.interfaceMatchImpliesSignatureEquality
            Pants.outerInnerMatch)
      }
  ; sectionReceipt = "actual two-ended original heterogeneous seam"
  }

heterogeneousMergeIncidence :
  {vertex : Vertex} {edge : Edge} →
  Fabric.incidence heterogeneousBeforeFabric vertex edge →
  Fabric.incidence heterogeneousMergedFabric
    vertex (Seam.mergeEdge edge)
heterogeneousMergeIncidence = Seam.mergeIncidence

heterogeneousMergePreservesRestrictions :
  {vertex : Vertex} {edge : Edge} →
  (incident : Fabric.incidence heterogeneousBeforeFabric vertex edge) →
  Seam.boundarySignature
    (realizeSourceEdge edge
      (Fabric.restrict heterogeneousBeforeFabric incident
        (Fabric.vertexValue heterogeneousBeforeSection vertex)))
  ≡
  Fabric.restrict heterogeneousMergedFabric
    (heterogeneousMergeIncidence incident)
    (Fabric.vertexValue heterogeneousMergedSection vertex)
heterogeneousMergePreservesRestrictions Seam.outerMembership = refl
heterogeneousMergePreservesRestrictions Seam.innerMembership = refl

heterogeneousMergePreservesEdgeValues :
  (edge : Edge) →
  Seam.boundarySignature
    (realizeSourceEdge edge
      (Fabric.edgeValue heterogeneousBeforeSection edge))
  ≡
  Fabric.edgeValue heterogeneousMergedSection (Seam.mergeEdge edge)
heterogeneousMergePreservesEdgeValues Seam.outerEdge = refl
heterogeneousMergePreservesEdgeValues Seam.innerEdge =
  sym (Seam.interfaceMatchImpliesSignatureEquality Pants.outerInnerMatch)

heterogeneousMergedProvenanceExact :
  Fabric.edgeProvenance heterogeneousMergedFabric Seam.mergedSeam
  ≡
  Fabric.edgeProvenance heterogeneousBeforeFabric Seam.outerEdge
  ++ Fabric.edgeProvenance heterogeneousBeforeFabric Seam.innerEdge
heterogeneousMergedProvenanceExact = refl

heterogeneousEdgesReallyMerge :
  Seam.mergeEdge Seam.outerEdge ≡ Seam.mergeEdge Seam.innerEdge
heterogeneousEdgesReallyMerge = refl

heterogeneousOuterIncidenceNonempty :
  Fabric.incidence heterogeneousMergedFabric
    Seam.outerSide Seam.mergedSeam
heterogeneousOuterIncidenceNonempty = Seam.outerMergedMembership

heterogeneousInnerIncidenceNonempty :
  Fabric.incidence heterogeneousMergedFabric
    Seam.innerSide Seam.mergedSeam
heterogeneousInnerIncidenceNonempty = Seam.innerMergedMembership

-- Explicit remaining boundary: the new merged stalk is the
-- matched five-field observation, not full BranchChannel and not
-- an automatically proved world/physical topology equivalence.
