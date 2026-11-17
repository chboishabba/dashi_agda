module DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact where

------------------------------------------------------------------------
-- A NON-VACUOUS finite topology-changing merge of the ORIGINAL
-- selected outer pants leg and inner pants waist, using the actual
-- five-coordinate InterfaceMatch already proved in-repo.
--
-- Two distinct incident edges are mapped to one shared seam edge;
-- BOTH vertices become incident to that seam. Full BranchChannel
-- equality is NOT asserted: source-specific labels, basins, and
-- receipts remain distinct. The merged edge stalk is the five-part
-- observable signature licensed by InterfaceMatch.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Reasoning.TypedHyperfabricCore as Fabric
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Physics.ShiftPhaseTableInterference as Phase
import DASHI.Reasoning.RelationalBranchInterference as Wave

SeamSignature : Set
SeamSignature =
  String × (Nat × (Phase.Phase4 × (Wave.BranchWave × Bool)))

boundarySignature : Pants.BranchChannel → SeamSignature
boundarySignature channel =
  Pants.propositionType (Pants.channelBoundary channel) ,
  (Pants.boundaryCapacity (Pants.channelBoundary channel) ,
  (Pants.boundaryPhase (Pants.channelBoundary channel) ,
  (Pants.channelWave channel ,
   Pants.boundaryOpen (Pants.channelBoundary channel))))

-- The existing source five-field seam pays for precisely this
-- equality, not full BranchChannel equality.
interfaceMatchImpliesSignatureEquality :
  {left right : Pants.BranchChannel} →
  Pants.InterfaceMatch left right →
  boundarySignature left ≡ boundarySignature right
interfaceMatchImpliesSignatureEquality matched =
  cong₂ _,_
    (Pants.InterfaceMatch.propositionMatches matched)
    (cong₂ _,_
      (Pants.InterfaceMatch.capacityMatches matched)
      (cong₂ _,_
        (Pants.InterfaceMatch.phaseMatches matched)
        (cong₂ _,_
          (Pants.InterfaceMatch.waveMatches matched)
          (Pants.InterfaceMatch.opennessMatches matched))))

data SeamSide : Set where
  outerSide innerSide : SeamSide

data BeforeSeamEdge : Set where
  outerEdge innerEdge : BeforeSeamEdge

data AfterSeamEdge : Set where
  mergedSeam : AfterSeamEdge

data BeforeIncidence : SeamSide → BeforeSeamEdge → Set where
  outerMembership : BeforeIncidence outerSide outerEdge
  innerMembership : BeforeIncidence innerSide innerEdge

data AfterIncidence : SeamSide → AfterSeamEdge → Set where
  outerMergedMembership : AfterIncidence outerSide mergedSeam
  innerMergedMembership : AfterIncidence innerSide mergedSeam

selectedSourceChannel : SeamSide → Pants.BranchChannel
selectedSourceChannel outerSide = Pants.selectedChannel2
selectedSourceChannel innerSide = Pants.innerInputChannel2

beforeSourceChannel : BeforeSeamEdge → Pants.BranchChannel
beforeSourceChannel outerEdge = Pants.selectedChannel2
beforeSourceChannel innerEdge = Pants.innerInputChannel2

-- The ORIGINAL donor's complete five-coordinate match is the
-- constructive provenance for this nontrivial edge merge.
originalMatchedSignatures :
  boundarySignature Pants.selectedChannel2
  ≡ boundarySignature Pants.innerInputChannel2
originalMatchedSignatures =
  interfaceMatchImpliesSignatureEquality Pants.outerInnerMatch

beforePantsFabric : Fabric.TypedHyperfabric SeamSide BeforeSeamEdge
beforePantsFabric = record
  { vertexStalk = λ side → Pants.BranchChannel
  ; edgeStalk = λ edge → Pants.BranchChannel
  ; incidence = BeforeIncidence
  ; restrict = λ
      { outerMembership channel → channel
      ; innerMembership channel → channel
      }
  ; edgeProvenance = λ
      { outerEdge → "outer selected pants leg" ∷ []
      ; innerEdge → "inner pants waist" ∷ []
      }
  ; edgeSalience = λ _ → 1
  ; fabricLabel = "original pair of incident pants boundaries before seam"
  }

beforePantsSection : Fabric.GlobalSection beforePantsFabric
beforePantsSection = record
  { vertexValue = selectedSourceChannel
  ; edgeValue = beforeSourceChannel
  ; compatible = λ
      { outerMembership → refl
      ; innerMembership → refl
      }
  ; sectionReceipt = "both edges possess actual source vertex incidence"
  }

afterPantsFabric : Fabric.TypedHyperfabric SeamSide AfterSeamEdge
afterPantsFabric = record
  { vertexStalk = λ side → Pants.BranchChannel
  ; edgeStalk = λ edge → SeamSignature
  ; incidence = AfterIncidence
  ; restrict = λ
      { outerMergedMembership channel → boundarySignature channel
      ; innerMergedMembership channel → boundarySignature channel
      }
  ; edgeProvenance = λ
      { mergedSeam →
          "outer selected pants leg" ∷
          "inner pants waist" ∷ [] }
  ; edgeSalience = λ _ → 1
  ; fabricLabel = "one merged seam with two actual endpoint incidences"
  }

afterPantsSection : Fabric.GlobalSection afterPantsFabric
afterPantsSection = record
  { vertexValue = selectedSourceChannel
  ; edgeValue = λ _ → boundarySignature Pants.selectedChannel2
  ; compatible = λ
      { outerMergedMembership → refl
      ; innerMergedMembership → sym originalMatchedSignatures
      }
  ; sectionReceipt = "five matched boundary observables restrict to one seam"
  }

-- Actual incidence transport from BOTH source edges into a
-- single post-merge edge, with no phantom/unproved incidence.
mergeEdge : BeforeSeamEdge → AfterSeamEdge
mergeEdge outerEdge = mergedSeam
mergeEdge innerEdge = mergedSeam

mergeIncidence :
  {side : SeamSide} {edge : BeforeSeamEdge} →
  BeforeIncidence side edge →
  AfterIncidence side (mergeEdge edge)
mergeIncidence outerMembership = outerMergedMembership
mergeIncidence innerMembership = innerMergedMembership

-- Original edge stalk data transports only to its licensed
-- five-coordinate signature. Provenance is retained separately.
seamRestrictionPreserved :
  {side : SeamSide} {edge : BeforeSeamEdge} →
  (membership : BeforeIncidence side edge) →
  boundarySignature
    (Fabric.restrict beforePantsFabric membership
      (Fabric.GlobalSection.vertexValue beforePantsSection side))
  ≡
  Fabric.restrict afterPantsFabric
    (mergeIncidence membership)
    (Fabric.GlobalSection.vertexValue afterPantsSection side)
seamRestrictionPreserved outerMembership = refl
seamRestrictionPreserved innerMembership = refl

seamEdgeValuePreserved :
  (edge : BeforeSeamEdge) →
  boundarySignature
    (Fabric.GlobalSection.edgeValue beforePantsSection edge)
  ≡
  Fabric.GlobalSection.edgeValue afterPantsSection (mergeEdge edge)
seamEdgeValuePreserved outerEdge = refl
seamEdgeValuePreserved innerEdge = sym originalMatchedSignatures

-- The merge really identifies two distinct original edge addresses.
sourceEdgesDistinct : ¬ (outerEdge ≡ innerEdge)
sourceEdgesDistinct ()

sourceEdgesHaveSameMergedAddress :
  mergeEdge outerEdge ≡ mergeEdge innerEdge
sourceEdgesHaveSameMergedAddress = refl

-- Provenance is not silently erased by quotienting the edge
-- address: both original receipts remain accessible at the seam.
mergedOuterProvenanceRetained :
  Fabric.edgeProvenance afterPantsFabric mergedSeam
  ≡ "outer selected pants leg" ∷ "inner pants waist" ∷ []
mergedOuterProvenanceRetained = refl

-- Concrete non-vacuity of the after-merge incidence at each end.
outerIsIncidentAfterMerge :
  AfterIncidence outerSide mergedSeam
outerIsIncidentAfterMerge = outerMergedMembership

innerIsIncidentAfterMerge :
  AfterIncidence innerSide mergedSeam
innerIsIncidentAfterMerge = innerMergedMembership
