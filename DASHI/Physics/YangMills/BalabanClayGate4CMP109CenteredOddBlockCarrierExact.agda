module DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthMap; lengthAppend; lengthCartesian; lengthAllCyclicIndices)

------------------------------------------------------------------------
-- Literal centred odd-side block carrier for CMP109 equation (0.3).
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - I. Small Fields",
-- arXiv:1108.1335v2 [math-ph]. No DOI recorded.
--
-- Bałaban and Dimock both use odd L and centred block coordinates.  Instead of
-- coercing the repository's side-2 parity carrier into that convention, this
-- module introduces the exact finite offset type
--
--   {-r,...,-1,0,1,...,r}
--
-- without importing an integer implementation.  A positive or negative offset
-- is a bounded index with r inhabitants, so the type has exactly 2r+1 values by
-- construction.  The fourfold product is the literal centred block.
------------------------------------------------------------------------

twice : Nat → Nat
twice zero = zero
twice (suc value) = suc (suc (twice value))

oddSide : Nat → Nat
oddSide radius = suc (twice radius)

square : Nat → Nat
square value = value * value

fourthPower : Nat → Nat
fourthPower value = square value * square value

addRightSuccessor : ∀ left right →
  left + suc right ≡ suc (left + right)
addRightSuccessor zero right = refl
addRightSuccessor (suc left) right =
  cong suc (addRightSuccessor left right)

selfAddEqualsTwice : ∀ value → value + value ≡ twice value
selfAddEqualsTwice zero = refl
selfAddEqualsTwice (suc value) =
  trans
    (cong suc (addRightSuccessor value value))
    (cong (λ result → suc (suc result))
      (selfAddEqualsTwice value))

radiusPlusSuccessorEqualsOddSide : ∀ radius →
  radius + suc radius ≡ oddSide radius
radiusPlusSuccessorEqualsOddSide radius =
  trans
    (addRightSuccessor radius radius)
    (cong suc (selfAddEqualsTwice radius))

data CenteredOffset (radius : Nat) : Set where
  centre : CenteredOffset radius
  positive : Carrier.CyclicIndex radius → CenteredOffset radius
  negative : Carrier.CyclicIndex radius → CenteredOffset radius

centeredOffsetRank : ∀ {radius} → Carrier.CyclicIndex radius → Nat
centeredOffsetRank Carrier.zeroᵢ = zero
centeredOffsetRank (Carrier.sucᵢ index) = suc (centeredOffsetRank index)

centeredOffsetMagnitude : ∀ {radius} → CenteredOffset radius → Nat
centeredOffsetMagnitude centre = zero
centeredOffsetMagnitude (positive index) = suc (centeredOffsetRank index)
centeredOffsetMagnitude (negative index) = suc (centeredOffsetRank index)

negativeOffsets : (radius : Nat) → List (CenteredOffset radius)
negativeOffsets radius =
  Carrier.map negative (Carrier.allCyclicIndices radius)

positiveOffsets : (radius : Nat) → List (CenteredOffset radius)
positiveOffsets radius =
  Carrier.map positive (Carrier.allCyclicIndices radius)

allCenteredOffsets : (radius : Nat) → List (CenteredOffset radius)
allCenteredOffsets radius =
  Carrier._++_ (negativeOffsets radius)
    (centre ∷ positiveOffsets radius)

allCenteredOffsetsComplete :
  ∀ {radius} (offset : CenteredOffset radius) →
  Carrier._∈_ offset (allCenteredOffsets radius)
allCenteredOffsetsComplete {radius} centre =
  Carrier.appendMembershipRight Carrier.here
allCenteredOffsetsComplete {radius} (positive index) =
  Carrier.appendMembershipRight
    (Carrier.there
      (Carrier.mapMembership positive
        (Carrier.allCyclicIndicesComplete index)))
allCenteredOffsetsComplete {radius} (negative index) =
  Carrier.appendMembershipLeft
    (Carrier.mapMembership negative
      (Carrier.allCyclicIndicesComplete index))

centeredOffsetFinite :
  ∀ radius → Carrier.FiniteEnumeration (CenteredOffset radius)
centeredOffsetFinite radius = record
  { elements = allCenteredOffsets radius
  ; complete = allCenteredOffsetsComplete
  }

CenteredBlockPoint4 : Nat → Set
CenteredBlockPoint4 radius = Carrier.Fourfold (CenteredOffset radius)

centeredBlockFinite :
  ∀ radius → Carrier.FiniteEnumeration (CenteredBlockPoint4 radius)
centeredBlockFinite radius =
  Carrier.productFinite
    (Carrier.productFinite
      (centeredOffsetFinite radius)
      (centeredOffsetFinite radius))
    (Carrier.productFinite
      (centeredOffsetFinite radius)
      (centeredOffsetFinite radius))

centeredOffsetEnumerationLength : ∀ radius →
  length (allCenteredOffsets radius) ≡ oddSide radius
centeredOffsetEnumerationLength radius
  rewrite lengthAppend (negativeOffsets radius)
    (centre ∷ positiveOffsets radius)
  | lengthMap negative (Carrier.allCyclicIndices radius)
  | lengthMap positive (Carrier.allCyclicIndices radius)
  | lengthAllCyclicIndices radius =
    radiusPlusSuccessorEqualsOddSide radius

centeredPairEnumerationLength : ∀ radius →
  length
    (Carrier.cartesian
      (allCenteredOffsets radius)
      (allCenteredOffsets radius))
  ≡ square (oddSide radius)
centeredPairEnumerationLength radius
  rewrite lengthCartesian
    (allCenteredOffsets radius)
    (allCenteredOffsets radius)
  | centeredOffsetEnumerationLength radius = refl

centeredBlockEnumerationLength : ∀ radius →
  length (Carrier.elements (centeredBlockFinite radius))
  ≡ fourthPower (oddSide radius)
centeredBlockEnumerationLength radius
  rewrite lengthCartesian
    (Carrier.cartesian
      (allCenteredOffsets radius)
      (allCenteredOffsets radius))
    (Carrier.cartesian
      (allCenteredOffsets radius)
      (allCenteredOffsets radius))
  | centeredPairEnumerationLength radius = refl

centeredOrigin4 : ∀ {radius} → CenteredBlockPoint4 radius
centeredOrigin4 =
  Carrier.pair
    (Carrier.pair centre centre)
    (Carrier.pair centre centre)

centeredBlockDisplayedSide : Nat → Nat
centeredBlockDisplayedSide = oddSide

centeredBlockDisplayedVolume : Nat → Nat
centeredBlockDisplayedVolume radius = fourthPower (oddSide radius)

record CMP109CenteredBlockConvention (radius : Nat) : Set₁ where
  field
    selectedPoints : Carrier.FiniteEnumeration (CenteredBlockPoint4 radius)
    selectedPointsExact : selectedPoints ≡ centeredBlockFinite radius
    displayedSideExact : Nat
    displayedSideMeaning : displayedSideExact ≡ oddSide radius
    displayedVolumeExact : Nat
    displayedVolumeMeaning :
      displayedVolumeExact ≡ fourthPower displayedSideExact

open CMP109CenteredBlockConvention public

canonicalCMP109CenteredBlockConvention :
  ∀ radius → CMP109CenteredBlockConvention radius
canonicalCMP109CenteredBlockConvention radius = record
  { selectedPoints = centeredBlockFinite radius
  ; selectedPointsExact = refl
  ; displayedSideExact = oddSide radius
  ; displayedSideMeaning = refl
  ; displayedVolumeExact = fourthPower (oddSide radius)
  ; displayedVolumeMeaning = refl
  }

cmp109CenteredOffsetCarrierLevel : ProofLevel
cmp109CenteredOffsetCarrierLevel = machineChecked

cmp109CenteredFourBlockFiniteLevel : ProofLevel
cmp109CenteredFourBlockFiniteLevel = machineChecked

cmp109CenteredBlockCardinalityLevel : ProofLevel
cmp109CenteredBlockCardinalityLevel = machineChecked

cmp109CenteredOddSideConventionLevel : ProofLevel
cmp109CenteredOddSideConventionLevel = machineChecked

physicalCMP109CenteredBlockToFineLatticeInputsLevel : ProofLevel
physicalCMP109CenteredBlockToFineLatticeInputsLevel = conditional
