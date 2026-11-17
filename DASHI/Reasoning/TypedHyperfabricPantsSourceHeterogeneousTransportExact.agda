module DASHI.Reasoning.TypedHyperfabricPantsSourceHeterogeneousTransportExact where

------------------------------------------------------------------------
-- H2.02 generic HETEROGENEOUS stalk-to-seam transport.
--
-- Original source-selected edge stalks can have DIFFERENT types.
-- Supply their authentic values, concrete interpretations into the
-- original BranchChannel, complete five-coordinate signature equality
-- (source evidence), and the two exact original provenance lists.
--
-- Then construct original HyperfabricPantsGluing, a before-fabric
-- with TWO genuine incidences, a topology-changing one-edge quotient,
-- and compatible before/after GlobalSections. Prove edge/restriction
-- commutation at both endpoints and preserve ordered provenance.
--
-- No fabricated world-node data or full-BranchChannel equality.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List.Base using (_++_)

import DASHI.Reasoning.TypedHyperfabricCore as Fabric
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as Gluing
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Geometry
import DASHI.Reasoning.TypedHyperfabricPantsSignatureCompletenessExact as Match
import DASHI.Reasoning.TypedHyperfabricOriginalHeterogeneousPantsSeamExact as Selected

module HeterogeneousMatchedSource
  (LeftStalk RightStalk : Set)
  (leftValue : LeftStalk)
  (rightValue : RightStalk)
  (leftInterpret : LeftStalk → Pants.BranchChannel)
  (rightInterpret : RightStalk → Pants.BranchChannel)
  (sourceSignatureAgreement :
    Geometry.boundarySignature (leftInterpret leftValue)
    ≡ Geometry.boundarySignature (rightInterpret rightValue))
  (leftProvenance rightProvenance : List String)
  where

  EdgeStalk : Geometry.BeforeSeamEdge → Set
  EdgeStalk Geometry.outerEdge = LeftStalk
  EdgeStalk Geometry.innerEdge = RightStalk

  VertexStalk : Geometry.SeamSide → Set
  VertexStalk Geometry.outerSide = LeftStalk
  VertexStalk Geometry.innerSide = RightStalk

  interpretEdge :
    (edge : Geometry.BeforeSeamEdge) →
    EdgeStalk edge → Pants.BranchChannel
  interpretEdge Geometry.outerEdge value = leftInterpret value
  interpretEdge Geometry.innerEdge value = rightInterpret value

  beforeFabric :
    Fabric.TypedHyperfabric
      Geometry.SeamSide Geometry.BeforeSeamEdge
  beforeFabric = record
    { vertexStalk = VertexStalk
    ; edgeStalk = EdgeStalk
    ; incidence = Geometry.BeforeIncidence
    ; restrict = λ
        { Geometry.outerMembership value → value
        ; Geometry.innerMembership value → value
        }
    ; edgeProvenance = λ
        { Geometry.outerEdge → leftProvenance
        ; Geometry.innerEdge → rightProvenance
        }
    ; edgeSalience = λ _ → 1
    ; fabricLabel = "source-typed heterogeneous boundary stalks"
    }

  beforeSection : Fabric.GlobalSection beforeFabric
  beforeSection = record
    { vertexValue = λ
        { Geometry.outerSide → leftValue
        ; Geometry.innerSide → rightValue
        }
    ; edgeValue = λ
        { Geometry.outerEdge → leftValue
        ; Geometry.innerEdge → rightValue
        }
    ; compatible = λ
        { Geometry.outerMembership → refl
        ; Geometry.innerMembership → refl
        }
    ; sectionReceipt = "selected original heterogeneous stalk values"
    }

  originalInterface :
    Pants.InterfaceMatch
      (leftInterpret leftValue)
      (rightInterpret rightValue)
  originalInterface =
    Match.signatureMatchComplete sourceSignatureAgreement

  admittedOriginalPantsSeam :
    Gluing.HyperfabricPantsGluing beforeSection
  admittedOriginalPantsSeam =
    Gluing.hyperfabric-pants-gluing
      Geometry.outerEdge
      Geometry.innerEdge
      interpretEdge
      originalInterface
      "five-field source equality constructs original InterfaceMatch"

  afterFabric :
    Fabric.TypedHyperfabric
      Geometry.SeamSide Geometry.AfterSeamEdge
  afterFabric = record
    { vertexStalk = VertexStalk
    ; edgeStalk = λ _ → Geometry.SeamSignature
    ; incidence = Geometry.AfterIncidence
    ; restrict = λ
        { Geometry.outerMergedMembership value →
            Geometry.boundarySignature (leftInterpret value)
        ; Geometry.innerMergedMembership value →
            Geometry.boundarySignature (rightInterpret value)
        }
    ; edgeProvenance = λ
        { Geometry.mergedSeam → leftProvenance ++ rightProvenance }
    ; edgeSalience = λ _ → 1
    ; fabricLabel = "source-preserving heterogeneous matched pants seam"
    }

  afterSection : Fabric.GlobalSection afterFabric
  afterSection = record
    { vertexValue = λ
        { Geometry.outerSide → leftValue
        ; Geometry.innerSide → rightValue
        }
    ; edgeValue = λ _ →
        Geometry.boundarySignature (leftInterpret leftValue)
    ; compatible = λ
        { Geometry.outerMergedMembership → refl
        ; Geometry.innerMergedMembership →
            sym sourceSignatureAgreement
        }
    ; sectionReceipt = "genuinely incident source-matched seam"
    }

  incidencePreserved :
    {vertex : Geometry.SeamSide}
    {edge : Geometry.BeforeSeamEdge} →
    Fabric.incidence beforeFabric vertex edge →
    Fabric.incidence afterFabric vertex (Geometry.mergeEdge edge)
  incidencePreserved = Geometry.mergeIncidence

  restrictionPreserved :
    {vertex : Geometry.SeamSide}
    {edge : Geometry.BeforeSeamEdge} →
    (incident : Fabric.incidence beforeFabric vertex edge) →
    Geometry.boundarySignature
      (interpretEdge edge
        (Fabric.restrict beforeFabric incident
          (Fabric.vertexValue beforeSection vertex)))
    ≡
    Fabric.restrict afterFabric (incidencePreserved incident)
      (Fabric.vertexValue afterSection vertex)
  restrictionPreserved Geometry.outerMembership = refl
  restrictionPreserved Geometry.innerMembership = refl

  edgeValuePreserved :
    (edge : Geometry.BeforeSeamEdge) →
    Geometry.boundarySignature
      (interpretEdge edge
        (Fabric.edgeValue beforeSection edge))
    ≡ Fabric.edgeValue afterSection (Geometry.mergeEdge edge)
  edgeValuePreserved Geometry.outerEdge = refl
  edgeValuePreserved Geometry.innerEdge =
    sym sourceSignatureAgreement

  entireSourceProvenanceRetained :
    Fabric.edgeProvenance afterFabric Geometry.mergedSeam
    ≡
    Fabric.edgeProvenance beforeFabric Geometry.outerEdge ++
    Fabric.edgeProvenance beforeFabric Geometry.innerEdge
  entireSourceProvenanceRetained = refl

  bothSourceEdgesReallyMerge :
    Geometry.mergeEdge Geometry.outerEdge
    ≡ Geometry.mergeEdge Geometry.innerEdge
  bothSourceEdgesReallyMerge = refl

-- Exact instantiation by the independently existing relational-pants
-- donor values and the source heterogenous fabric's provenance.
module OriginalRelationalPants =
  HeterogeneousMatchedSource
    Pants.BoundaryInterface
    Pants.BranchChannel
    Pants.selectedBoundary2
    Pants.innerInputChannel2
    Selected.realizeOriginalBoundary
    (λ channel → channel)
    Selected.sourceRealizedEdgesMatch
    (Fabric.edgeProvenance
      Selected.heterogeneousBeforeFabric Geometry.outerEdge)
    (Fabric.edgeProvenance
      Selected.heterogeneousBeforeFabric Geometry.innerEdge)

originalWorldFreeHeterogeneousSeam :
  Gluing.HyperfabricPantsGluing OriginalRelationalPants.beforeSection
originalWorldFreeHeterogeneousSeam =
  OriginalRelationalPants.admittedOriginalPantsSeam

originalRelationalHeterogeneousProvenanceRetained :
  Fabric.edgeProvenance OriginalRelationalPants.afterFabric
    Geometry.mergedSeam
  ≡
  Fabric.edgeProvenance OriginalRelationalPants.beforeFabric
    Geometry.outerEdge ++
  Fabric.edgeProvenance OriginalRelationalPants.beforeFabric
    Geometry.innerEdge
originalRelationalHeterogeneousProvenanceRetained =
  OriginalRelationalPants.entireSourceProvenanceRetained
