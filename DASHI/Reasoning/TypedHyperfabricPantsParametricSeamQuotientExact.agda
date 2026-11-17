module DASHI.Reasoning.TypedHyperfabricPantsParametricSeamQuotientExact where

-- Generalise the existing concrete pants seam specimen to ANY two source
-- BranchChannel values accompanied by their actual five-field InterfaceMatch.
-- All constructions are original TypedHyperfabricCore fabrics/sections.
-- No equality of full channel records, nor group or world semantics, is assumed.

open import DASHI.Core.Prelude
import DASHI.Reasoning.TypedHyperfabricCore as Fabric
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Seam

module MatchedSeam
  (left right : Pants.BranchChannel)
  (matched : Pants.InterfaceMatch left right) where

  sourceChannel : Seam.SeamSide → Pants.BranchChannel
  sourceChannel Seam.outerSide = left
  sourceChannel Seam.innerSide = right

  sourceEdgeChannel : Seam.BeforeSeamEdge → Pants.BranchChannel
  sourceEdgeChannel Seam.outerEdge = left
  sourceEdgeChannel Seam.innerEdge = right

  matchedSignatures :
    Seam.boundarySignature left ≡ Seam.boundarySignature right
  matchedSignatures = Seam.interfaceMatchImpliesSignatureEquality matched

  beforeFabric :
    Fabric.TypedHyperfabric Seam.SeamSide Seam.BeforeSeamEdge
  beforeFabric = record
    { vertexStalk = λ _ → Pants.BranchChannel
    ; edgeStalk = λ _ → Pants.BranchChannel
    ; incidence = Seam.BeforeIncidence
    ; restrict = λ
        { Seam.outerMembership channel → channel
        ; Seam.innerMembership channel → channel
        }
    ; edgeProvenance = λ
        { Seam.outerEdge → "matched seam: original left edge" ∷ []
        ; Seam.innerEdge → "matched seam: original right edge" ∷ []
        }
    ; edgeSalience = λ _ → 1
    ; fabricLabel = "parameterized source pants boundaries before merge"
    }

  beforeSection : Fabric.GlobalSection beforeFabric
  beforeSection = record
    { vertexValue = sourceChannel
    ; edgeValue = sourceEdgeChannel
    ; compatible = λ
        { Seam.outerMembership → refl
        ; Seam.innerMembership → refl
        }
    ; sectionReceipt = "original source channels at distinct incident edges"
    }

  afterFabric :
    Fabric.TypedHyperfabric Seam.SeamSide Seam.AfterSeamEdge
  afterFabric = record
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
            "matched seam: original left edge" ∷
            "matched seam: original right edge" ∷ []
        }
    ; edgeSalience = λ _ → 1
    ; fabricLabel = "parameterized matched-source two-incidence seam quotient"
    }

  afterSection : Fabric.GlobalSection afterFabric
  afterSection = record
    { vertexValue = sourceChannel
    ; edgeValue = λ _ → Seam.boundarySignature left
    ; compatible = λ
        { Seam.outerMergedMembership → refl
        ; Seam.innerMergedMembership → sym matchedSignatures
        }
    ; sectionReceipt = "two actual incidences agree through five-field match"
    }

  preserveIncidence :
    {side : Seam.SeamSide} {edge : Seam.BeforeSeamEdge} →
    Seam.BeforeIncidence side edge →
    Seam.AfterIncidence side (Seam.mergeEdge edge)
  preserveIncidence = Seam.mergeIncidence

  preserveVertexRestriction :
    {side : Seam.SeamSide} {edge : Seam.BeforeSeamEdge} →
    (incident : Seam.BeforeIncidence side edge) →
    Seam.boundarySignature
      (Fabric.restrict beforeFabric incident
        (Fabric.vertexValue beforeSection side))
    ≡
    Fabric.restrict afterFabric (preserveIncidence incident)
      (Fabric.vertexValue afterSection side)
  preserveVertexRestriction Seam.outerMembership = refl
  preserveVertexRestriction Seam.innerMembership = refl

  preserveEdgeValue :
    (edge : Seam.BeforeSeamEdge) →
    Seam.boundarySignature (Fabric.edgeValue beforeSection edge)
    ≡ Fabric.edgeValue afterSection (Seam.mergeEdge edge)
  preserveEdgeValue Seam.outerEdge = refl
  preserveEdgeValue Seam.innerEdge = sym matchedSignatures

  bothOriginalEdgesIdentify :
    Seam.mergeEdge Seam.outerEdge ≡ Seam.mergeEdge Seam.innerEdge
  bothOriginalEdgesIdentify = refl

  originalLeftIncidentAfter :
    Seam.AfterIncidence Seam.outerSide Seam.mergedSeam
  originalLeftIncidentAfter = Seam.outerMergedMembership

  originalRightIncidentAfter :
    Seam.AfterIncidence Seam.innerSide Seam.mergedSeam
  originalRightIncidentAfter = Seam.innerMergedMembership

-- Specialize to the ORIGINAL canonical donor's actual match.
canonicalMatchedSeamPreservesLeft :
  Seam.boundarySignature Pants.selectedChannel2 ≡
  Fabric.edgeValue
    (MatchedSeam.afterSection
      Pants.selectedChannel2 Pants.innerInputChannel2 Pants.outerInnerMatch)
    Seam.mergedSeam
canonicalMatchedSeamPreservesLeft = refl

canonicalMatchedSeamPreservesRight :
  Seam.boundarySignature Pants.innerInputChannel2 ≡
  Fabric.edgeValue
    (MatchedSeam.afterSection
      Pants.selectedChannel2 Pants.innerInputChannel2 Pants.outerInnerMatch)
    Seam.mergedSeam
canonicalMatchedSeamPreservesRight =
  sym (MatchedSeam.matchedSignatures
    Pants.selectedChannel2 Pants.innerInputChannel2 Pants.outerInnerMatch)
