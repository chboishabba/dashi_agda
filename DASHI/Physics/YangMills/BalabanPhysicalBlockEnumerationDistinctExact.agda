module DASHI.Physics.YangMills.BalabanPhysicalBlockEnumerationDistinctExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier

------------------------------------------------------------------------
-- Duplicate-free proofs for the literal physical block enumerations.
------------------------------------------------------------------------

pairCyclicIndicesDuplicateFree : ∀ L →
  DuplicateFree
    (cartesian (allCyclicIndices L) (allCyclicIndices L))
pairCyclicIndicesDuplicateFree L =
  cartesianDuplicateFree
    (allCyclicIndicesDuplicateFree L)
    (allCyclicIndicesDuplicateFree L)

physicalBlockSitesDuplicateFree : ∀ L →
  DuplicateFree (physicalBlockSites L)
physicalBlockSitesDuplicateFree L =
  cartesianDuplicateFree
    (pairCyclicIndicesDuplicateFree L)
    (pairCyclicIndicesDuplicateFree L)

physicalTransverseCoordinatesDuplicateFree : ∀ L →
  DuplicateFree (physicalTransverseCoordinates L)
physicalTransverseCoordinatesDuplicateFree L =
  cartesianDuplicateFree
    (allCyclicIndicesDuplicateFree L)
    (pairCyclicIndicesDuplicateFree L)

physicalAxisFibreDuplicateFree : ∀ {L} axis transverse →
  DuplicateFree (physicalAxisFibre {L} axis transverse)
physicalAxisFibreDuplicateFree {L} axis transverse =
  mapDuplicateFree
    (insertAxisCoordinateInjective axis transverse)
    (allCyclicIndicesDuplicateFree L)

physicalFibreEnumerationDuplicateFree : ∀ L →
  DuplicateFree (physicalFibreEnumeration L)
physicalFibreEnumerationDuplicateFree L =
  cartesianDuplicateFree
    (allCyclicIndicesDuplicateFree four)
    (physicalTransverseCoordinatesDuplicateFree L)

makePhysicalPositiveEdgeInjective :
  ∀ {n} {left right :
    Product Axis4
      (Product (Triple (CyclicIndex (suc n))) (CyclicIndex n))} →
  makePhysicalPositiveEdge left ≡ makePhysicalPositiveEdge right →
  left ≡ right
makePhysicalPositiveEdgeInjective refl = refl

physicalPositiveEdgesDuplicateFree : ∀ L →
  DuplicateFree (physicalPositiveEdges L)
physicalPositiveEdgesDuplicateFree zero = []-free
physicalPositiveEdgesDuplicateFree (suc n) =
  mapDuplicateFree
    makePhysicalPositiveEdgeInjective
    (cartesianDuplicateFree
      (allCyclicIndicesDuplicateFree four)
      (cartesianDuplicateFree
        (physicalTransverseCoordinatesDuplicateFree (suc n))
        (allCyclicIndicesDuplicateFree n)))

physicalBlockSitesDuplicateFreeLevel : ProofLevel
physicalBlockSitesDuplicateFreeLevel = machineChecked

physicalAxisFibreDuplicateFreeLevel : ProofLevel
physicalAxisFibreDuplicateFreeLevel = machineChecked

physicalFibreEnumerationDuplicateFreeLevel : ProofLevel
physicalFibreEnumerationDuplicateFreeLevel = machineChecked

physicalPositiveEdgesDuplicateFreeLevel : ProofLevel
physicalPositiveEdgesDuplicateFreeLevel = machineChecked
