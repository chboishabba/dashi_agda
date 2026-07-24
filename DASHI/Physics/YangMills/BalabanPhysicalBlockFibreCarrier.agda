module DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_) 
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthMap; lengthCartesian; lengthAllCyclicIndices)

------------------------------------------------------------------------
-- Literal open L^4 block carrier and its one-dimensional axis fibres.
--
-- The site carrier is the repository's concrete fourfold finite product.  A
-- transverse coordinate contains the three coordinates not varied by a chosen
-- axis.  The insertion/extraction round trips below identify every physical
-- site with one and only one coordinate on its corresponding axis fibre.
------------------------------------------------------------------------

Triple : Set → Set
Triple A = Product A (Product A A)

PhysicalBlockL : Nat → Set
PhysicalBlockL = periodicTorus4Definition

physicalBlockSites : (L : Nat) → List (PhysicalBlockL L)
physicalBlockSites L = elements (periodicTorus4Finite L)

physicalBlockSitesComplete : ∀ {L} (site : PhysicalBlockL L) →
  site ∈ physicalBlockSites L
physicalBlockSitesComplete {L} = complete (periodicTorus4Finite L)

physicalTransverseCoordinates : (L : Nat) → List (Triple (CyclicIndex L))
physicalTransverseCoordinates L =
  cartesian (allCyclicIndices L)
    (cartesian (allCyclicIndices L) (allCyclicIndices L))

physicalTransverseCoordinatesComplete :
  ∀ {L} (coordinate : Triple (CyclicIndex L)) →
  coordinate ∈ physicalTransverseCoordinates L
physicalTransverseCoordinatesComplete (pair x (pair y z)) =
  cartesianMembership
    (allCyclicIndicesComplete x)
    (cartesianMembership
      (allCyclicIndicesComplete y)
      (allCyclicIndicesComplete z))

cubeCount : Nat → Nat
cubeCount L = L * (L * L)

physicalTransverseCoordinateCount : ∀ L →
  length (physicalTransverseCoordinates L) ≡ cubeCount L
physicalTransverseCoordinateCount L
  rewrite lengthCartesian
    (allCyclicIndices L)
    (cartesian (allCyclicIndices L) (allCyclicIndices L))
  | lengthAllCyclicIndices L
  | lengthCartesian (allCyclicIndices L) (allCyclicIndices L)
  | lengthAllCyclicIndices L = refl

insertAxis :
  ∀ {L} → Axis4 → CyclicIndex L → Triple (CyclicIndex L) →
  PhysicalBlockL L
insertAxis zeroᵢ t (pair x1 (pair x2 x3)) =
  pair (pair t x1) (pair x2 x3)
insertAxis (sucᵢ zeroᵢ) t (pair x0 (pair x2 x3)) =
  pair (pair x0 t) (pair x2 x3)
insertAxis (sucᵢ (sucᵢ zeroᵢ)) t (pair x0 (pair x1 x3)) =
  pair (pair x0 x1) (pair t x3)
insertAxis (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) t (pair x0 (pair x1 x2)) =
  pair (pair x0 x1) (pair x2 t)

axisCoordinate : ∀ {L} → Axis4 → PhysicalBlockL L → CyclicIndex L
axisCoordinate zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = x0
axisCoordinate (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) = x1
axisCoordinate (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) = x2
axisCoordinate (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = x3

axisTransverse :
  ∀ {L} → Axis4 → PhysicalBlockL L → Triple (CyclicIndex L)
axisTransverse zeroᵢ (pair (pair x0 x1) (pair x2 x3)) =
  pair x1 (pair x2 x3)
axisTransverse (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) =
  pair x0 (pair x2 x3)
axisTransverse (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) =
  pair x0 (pair x1 x3)
axisTransverse (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) =
  pair x0 (pair x1 x2)

insertExtractAxis : ∀ {L} axis (site : PhysicalBlockL L) →
  insertAxis axis (axisCoordinate axis site) (axisTransverse axis site) ≡ site
insertExtractAxis zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = refl
insertExtractAxis (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) = refl
insertExtractAxis (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
insertExtractAxis (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl

extractInsertCoordinate : ∀ {L} axis coordinate transverse →
  axisCoordinate axis (insertAxis axis coordinate transverse) ≡ coordinate
extractInsertCoordinate zeroᵢ coordinate (pair x1 (pair x2 x3)) = refl
extractInsertCoordinate (sucᵢ zeroᵢ) coordinate (pair x0 (pair x2 x3)) = refl
extractInsertCoordinate (sucᵢ (sucᵢ zeroᵢ)) coordinate
  (pair x0 (pair x1 x3)) = refl
extractInsertCoordinate (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) coordinate
  (pair x0 (pair x1 x2)) = refl

extractInsertTransverse : ∀ {L} axis coordinate transverse →
  axisTransverse axis (insertAxis axis coordinate transverse) ≡ transverse
extractInsertTransverse zeroᵢ coordinate (pair x1 (pair x2 x3)) = refl
extractInsertTransverse (sucᵢ zeroᵢ) coordinate (pair x0 (pair x2 x3)) = refl
extractInsertTransverse (sucᵢ (sucᵢ zeroᵢ)) coordinate
  (pair x0 (pair x1 x3)) = refl
extractInsertTransverse (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) coordinate
  (pair x0 (pair x1 x2)) = refl

physicalAxisFibre :
  ∀ {L} → Axis4 → Triple (CyclicIndex L) → List (PhysicalBlockL L)
physicalAxisFibre {L} axis transverse =
  map (λ coordinate → insertAxis axis coordinate transverse)
    (allCyclicIndices L)

physicalAxisFibreLength : ∀ {L} axis transverse →
  length (physicalAxisFibre {L} axis transverse) ≡ L
physicalAxisFibreLength {L} axis transverse =
  trans
    (lengthMap
      (λ coordinate → insertAxis axis coordinate transverse)
      (allCyclicIndices L))
    (lengthAllCyclicIndices L)

physicalAxisFibreContainsSite : ∀ {L} axis (site : PhysicalBlockL L) →
  site ∈ physicalAxisFibre axis (axisTransverse axis site)
physicalAxisFibreContainsSite {L} axis site =
  subst
    (λ candidate →
      candidate ∈ physicalAxisFibre axis (axisTransverse axis site))
    (insertExtractAxis axis site)
    (mapMembership
      (λ coordinate → insertAxis axis coordinate (axisTransverse axis site))
      (allCyclicIndicesComplete (axisCoordinate axis site)))

insertAxisCoordinateInjective :
  ∀ {L} axis transverse {left right : CyclicIndex L} →
  insertAxis axis left transverse ≡ insertAxis axis right transverse →
  left ≡ right
insertAxisCoordinateInjective zeroᵢ transverse refl = refl
insertAxisCoordinateInjective (sucᵢ zeroᵢ) transverse refl = refl
insertAxisCoordinateInjective (sucᵢ (sucᵢ zeroᵢ)) transverse refl = refl
insertAxisCoordinateInjective (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) transverse refl = refl

------------------------------------------------------------------------
-- The literal family of all four-axis fibres.
------------------------------------------------------------------------

PhysicalFibre : Nat → Set
PhysicalFibre L = Product Axis4 (Triple (CyclicIndex L))

physicalFibreEnumeration : (L : Nat) → List (PhysicalFibre L)
physicalFibreEnumeration L =
  cartesian (allCyclicIndices four) (physicalTransverseCoordinates L)

physicalFibreEnumerationComplete : ∀ {L} (fibre : PhysicalFibre L) →
  fibre ∈ physicalFibreEnumeration L
physicalFibreEnumerationComplete (pair axis transverse) =
  cartesianMembership
    (allCyclicIndicesComplete axis)
    (physicalTransverseCoordinatesComplete transverse)

physicalFibreSites : ∀ {L} → PhysicalFibre L → List (PhysicalBlockL L)
physicalFibreSites (pair axis transverse) = physicalAxisFibre axis transverse

physicalFibreCount : Nat → Nat
physicalFibreCount L = four * cubeCount L

physicalFibreEnumerationLength : ∀ L →
  length (physicalFibreEnumeration L) ≡ physicalFibreCount L
physicalFibreEnumerationLength L
  rewrite lengthCartesian
    (allCyclicIndices four)
    (physicalTransverseCoordinates L)
  | lengthAllCyclicIndices four
  | physicalTransverseCoordinateCount L = refl

------------------------------------------------------------------------
-- Literal positive open-block edges.  A predecessor in CyclicIndex n denotes
-- the edge from its order-preserving embedding in CyclicIndex (suc n) to its
-- successor.  Consequently there are L-1 edges on every length-L fibre.
------------------------------------------------------------------------

weakenIndex : ∀ {n} → CyclicIndex n → CyclicIndex (suc n)
weakenIndex {zero} ()
weakenIndex {suc n} zeroᵢ = zeroᵢ
weakenIndex {suc n} (sucᵢ index) = sucᵢ (weakenIndex index)

data PhysicalPositiveEdge : Nat → Set where
  positiveEdge : ∀ {n} →
    Axis4 → Triple (CyclicIndex (suc n)) → CyclicIndex n →
    PhysicalPositiveEdge (suc n)

positiveEdgeStart : ∀ {L} → PhysicalPositiveEdge L → PhysicalBlockL L
positiveEdgeStart (positiveEdge axis transverse predecessor) =
  insertAxis axis (weakenIndex predecessor) transverse

positiveEdgeEnd : ∀ {L} → PhysicalPositiveEdge L → PhysicalBlockL L
positiveEdgeEnd (positiveEdge axis transverse predecessor) =
  insertAxis axis (sucᵢ predecessor) transverse

makePhysicalPositiveEdge : ∀ {n} →
  Product Axis4
    (Product (Triple (CyclicIndex (suc n))) (CyclicIndex n)) →
  PhysicalPositiveEdge (suc n)
makePhysicalPositiveEdge (pair axis (pair transverse predecessor)) =
  positiveEdge axis transverse predecessor

physicalPositiveEdges : (L : Nat) → List (PhysicalPositiveEdge L)
physicalPositiveEdges zero = []
physicalPositiveEdges (suc n) =
  map makePhysicalPositiveEdge
    (cartesian
      (allCyclicIndices four)
      (cartesian
        (physicalTransverseCoordinates (suc n))
        (allCyclicIndices n)))

physicalPositiveEdgesComplete : ∀ {L} (edge : PhysicalPositiveEdge L) →
  edge ∈ physicalPositiveEdges L
physicalPositiveEdgesComplete
  (positiveEdge {n} axis transverse predecessor) =
  mapMembership makePhysicalPositiveEdge
    (cartesianMembership
      (allCyclicIndicesComplete axis)
      (cartesianMembership
        (physicalTransverseCoordinatesComplete transverse)
        (allCyclicIndicesComplete predecessor)))

pathEdgeCount : Nat → Nat
pathEdgeCount zero = zero
pathEdgeCount (suc n) = n

physicalPositiveEdgeCount : Nat → Nat
physicalPositiveEdgeCount L =
  four * (cubeCount L * pathEdgeCount L)

physicalPositiveEdgesLength : ∀ L →
  length (physicalPositiveEdges L) ≡ physicalPositiveEdgeCount L
physicalPositiveEdgesLength zero = refl
physicalPositiveEdgesLength (suc n)
  rewrite lengthMap makePhysicalPositiveEdge
    (cartesian
      (allCyclicIndices four)
      (cartesian
        (physicalTransverseCoordinates (suc n))
        (allCyclicIndices n)))
  | lengthCartesian
      (allCyclicIndices four)
      (cartesian
        (physicalTransverseCoordinates (suc n))
        (allCyclicIndices n))
  | lengthAllCyclicIndices four
  | lengthCartesian
      (physicalTransverseCoordinates (suc n))
      (allCyclicIndices n)
  | physicalTransverseCoordinateCount (suc n)
  | lengthAllCyclicIndices n = refl

physicalBlockSiteEnumerationLevel : ProofLevel
physicalBlockSiteEnumerationLevel = machineChecked

physicalAxisFibreCarrierLevel : ProofLevel
physicalAxisFibreCarrierLevel = machineChecked

physicalPositiveEdgeEnumerationLevel : ProofLevel
physicalPositiveEdgeEnumerationLevel = machineChecked

physicalBlockEnumerationDuplicateFreeLevel : ProofLevel
physicalBlockEnumerationDuplicateFreeLevel = conditional
