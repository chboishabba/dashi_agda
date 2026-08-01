module DASHI.Physics.YangMills.BalabanClayGate4CMP109ContourLengthExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic

------------------------------------------------------------------------
-- Exact length of every enumerated CMP109 shortest contour.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Every active coordinate segment is straight and has its displacement count
-- as length.  Insertion permutations preserve the sum of those counts, so all
-- enumerated contour words have exactly the same length:
--
--   |word(order)| = sum_mu |delta_mu|.
--
-- This replaces a contour-by-contour path-length assumption in the principal
-- chart and holonomy derivative bounds.  A source block convention only has to
-- bound the four coordinate displacement counts.
------------------------------------------------------------------------

addNat : Nat → Nat → Nat
addNat zero right = right
addNat (suc left) right = suc (addNat left right)

addNatAssociative : ∀ left middle right →
  addNat (addNat left middle) right
  ≡ addNat left (addNat middle right)
addNatAssociative zero middle right = refl
addNatAssociative (suc left) middle right =
  cong suc (addNatAssociative left middle right)

addNatSwapSuccessor : ∀ left right →
  addNat left (suc right) ≡ suc (addNat left right)
addNatSwapSuccessor zero right = refl
addNatSwapSuccessor (suc left) right =
  cong suc (addNatSwapSuccessor left right)

addNatCommutative : ∀ left right →
  addNat left right ≡ addNat right left
addNatCommutative zero zero = refl
addNatCommutative zero (suc right) =
  cong suc (addNatCommutative zero right)
addNatCommutative (suc left) right =
  trans
    (cong suc (addNatCommutative left right))
    (symmetry (addNatSwapSuccessor right left))
  where
  symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symmetry refl = refl

segmentCountSum : List Contours.AxisSegment → Nat
segmentCountSum [] = zero
segmentCountSum (segment ∷ segments) =
  addNat
    (Contours.count (Contours.segmentCount segment))
    (segmentCountSum segments)

periodicAppendLength :
  ∀ {A : Set} (left right : List A) →
  Periodic.listLength (Periodic._++_ left right)
  ≡ addNat (Periodic.listLength left) (Periodic.listLength right)
periodicAppendLength [] right = refl
periodicAppendLength (value ∷ values) right =
  cong suc (periodicAppendLength values right)

contourWordLengthEqualsSegmentCountSum :
  ∀ segments →
  Periodic.listLength (Periodic.contourWord segments)
  ≡ segmentCountSum segments
contourWordLengthEqualsSegmentCountSum [] = refl
contourWordLengthEqualsSegmentCountSum (segment ∷ segments) =
  trans
    (periodicAppendLength
      (Periodic.segmentWord segment)
      (Periodic.contourWord segments))
    (trans
      (cong
        (λ count → addNat count
          (Periodic.listLength (Periodic.contourWord segments)))
        (Periodic.segmentWordLength segment))
      (cong
        (addNat (Contours.count (Contours.segmentCount segment)))
        (contourWordLengthEqualsSegmentCountSum segments)))

insertionPreservesSegmentCountSum :
  ∀ {value source inserted} →
  Contours.Insertion value source inserted →
  segmentCountSum inserted
  ≡ addNat
      (Contours.count (Contours.segmentCount value))
      (segmentCountSum source)
insertionPreservesSegmentCountSum Contours.insertHere = refl
insertionPreservesSegmentCountSum
    (Contours.insertThere {other = other} insertion) =
  trans
    (cong
      (addNat (Contours.count (Contours.segmentCount other)))
      (insertionPreservesSegmentCountSum insertion))
    (trans
      (symmetry
        (addNatAssociative
          (Contours.count (Contours.segmentCount other))
          (Contours.count (Contours.segmentCount _))
          (segmentCountSum _)))
      (trans
        (cong
          (λ middle → addNat middle (segmentCountSum _))
          (addNatCommutative
            (Contours.count (Contours.segmentCount other))
            (Contours.count (Contours.segmentCount _))))
        (addNatAssociative
          (Contours.count (Contours.segmentCount _))
          (Contours.count (Contours.segmentCount other))
          (segmentCountSum _))))
  where
  symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symmetry refl = refl

generatedPermutationPreservesSegmentCountSum :
  ∀ {source order} →
  Contours.GeneratedPermutation source order →
  segmentCountSum order ≡ segmentCountSum source
generatedPermutationPreservesSegmentCountSum Contours.permutationNil = refl
generatedPermutationPreservesSegmentCountSum
    (Contours.permutationInsert permutation insertion) =
  trans
    (insertionPreservesSegmentCountSum insertion)
    (cong
      (addNat (Contours.count (Contours.segmentCount _)))
      (generatedPermutationPreservesSegmentCountSum permutation))

enumeratedContourWordLengthExact :
  ∀ displacement order →
  Contours._∈_ order
    (Contours.cmp109ShortestContourOrders displacement) →
  Periodic.listLength (Periodic.contourWord order)
  ≡ segmentCountSum (Contours.activeSegments displacement)
enumeratedContourWordLengthExact displacement order membership =
  trans
    (contourWordLengthEqualsSegmentCountSum order)
    (generatedPermutationPreservesSegmentCountSum
      (Contours.cmp109ContourOrderSound displacement order membership))

cmp109ContourWordLengthLevel : ProofLevel
cmp109ContourWordLengthLevel = machineChecked

cmp109ContourLengthPermutationInvariantLevel : ProofLevel
cmp109ContourLengthPermutationInvariantLevel = machineChecked

physicalCMP109CoordinateDisplacementBoundInputsLevel : ProofLevel
physicalCMP109CoordinateDisplacementBoundInputsLevel = conditional
