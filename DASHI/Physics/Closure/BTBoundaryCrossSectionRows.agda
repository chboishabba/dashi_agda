module DASHI.Physics.Closure.BTBoundaryCrossSectionRows where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BTCanonicalNeckAnalogue as Neck
import DASHI.Physics.Closure.HolographicBulkBoundaryReceipt as Boundary

------------------------------------------------------------------------
-- Finite p-adic boundary/cross-section rows for the p = 2, 3, 7 lanes.
--
-- These rows record the BT finite neighbor-sphere cross-section p + 1
-- alongside the p-adic boundary label P^1(Q_p).  They are bookkeeping
-- rows only: no smooth S2 boundary and no Archimedean S2 identification
-- is promoted here.

length : {A : Set} → List A → Nat
length [] =
  0
length (_ ∷ xs) =
  suc (length xs)

p2BoundaryLabel : String
p2BoundaryLabel =
  "P^1(Q_2)"

p3BoundaryLabel : String
p3BoundaryLabel =
  "P^1(Q_3)"

p7BoundaryLabel : String
p7BoundaryLabel =
  "P^1(Q_7)"

boundaryLabelForLane : Neck.BTPrimeLane → String
boundaryLabelForLane Neck.p2Lane =
  p2BoundaryLabel
boundaryLabelForLane Neck.p3Lane =
  p3BoundaryLabel
boundaryLabelForLane Neck.p7Lane =
  p7BoundaryLabel

record BTBoundaryCrossSectionRow : Set where
  field
    primeLane :
      Neck.BTPrimeLane

    pValue :
      Nat

    pValueIsPrimeLaneValue :
      pValue ≡ Neck.primeValue primeLane

    crossSectionCardinality :
      Nat

    crossSectionCardinalityIsPPlusOne :
      crossSectionCardinality ≡ suc pValue

    canonicalNeck :
      Neck.BTCanonicalNeckAnalogue

    canonicalNeckIsLaneDepthZero :
      canonicalNeck ≡ Neck.canonicalBTNeckAnalogueAt primeLane 0

    crossSectionMatchesNeck :
      crossSectionCardinality
      ≡
      Neck.crossSectionCardinality canonicalNeck

    boundaryLabel :
      String

    boundaryLabelIsForLane :
      boundaryLabel ≡ boundaryLabelForLane primeLane

    carrierBoundaryProduct :
      String

    carrierBoundaryProductIsCanonical :
      carrierBoundaryProduct
      ≡
      Boundary.carrierBoundaryProduct
        Boundary.canonicalHolographicBulkBoundaryReceipt

    smoothS2BoundaryPromoted :
      Bool

    smoothS2BoundaryPromotedIsFalse :
      smoothS2BoundaryPromoted ≡ false

    archimedeanS2Identification :
      Bool

    archimedeanS2IdentificationIsFalse :
      archimedeanS2Identification ≡ false

open BTBoundaryCrossSectionRow public

btBoundaryCrossSectionRow :
  Neck.BTPrimeLane →
  BTBoundaryCrossSectionRow
btBoundaryCrossSectionRow lane =
  record
    { primeLane =
        lane
    ; pValue =
        Neck.primeValue lane
    ; pValueIsPrimeLaneValue =
        refl
    ; crossSectionCardinality =
        Neck.crossSectionCardinality
          (Neck.canonicalBTNeckAnalogueAt lane 0)
    ; crossSectionCardinalityIsPPlusOne =
        refl
    ; canonicalNeck =
        Neck.canonicalBTNeckAnalogueAt lane 0
    ; canonicalNeckIsLaneDepthZero =
        refl
    ; crossSectionMatchesNeck =
        refl
    ; boundaryLabel =
        boundaryLabelForLane lane
    ; boundaryLabelIsForLane =
        refl
    ; carrierBoundaryProduct =
        Boundary.carrierBoundaryProduct
          Boundary.canonicalHolographicBulkBoundaryReceipt
    ; carrierBoundaryProductIsCanonical =
        refl
    ; smoothS2BoundaryPromoted =
        false
    ; smoothS2BoundaryPromotedIsFalse =
        refl
    ; archimedeanS2Identification =
        false
    ; archimedeanS2IdentificationIsFalse =
        refl
    }

p2BoundaryCrossSectionRow : BTBoundaryCrossSectionRow
p2BoundaryCrossSectionRow =
  btBoundaryCrossSectionRow Neck.p2Lane

p3BoundaryCrossSectionRow : BTBoundaryCrossSectionRow
p3BoundaryCrossSectionRow =
  btBoundaryCrossSectionRow Neck.p3Lane

p7BoundaryCrossSectionRow : BTBoundaryCrossSectionRow
p7BoundaryCrossSectionRow =
  btBoundaryCrossSectionRow Neck.p7Lane

canonicalBTBoundaryCrossSectionRows :
  List BTBoundaryCrossSectionRow
canonicalBTBoundaryCrossSectionRows =
  p2BoundaryCrossSectionRow
  ∷ p3BoundaryCrossSectionRow
  ∷ p7BoundaryCrossSectionRow
  ∷ []

canonicalBTBoundaryCrossSectionRowCountIs3 :
  length canonicalBTBoundaryCrossSectionRows ≡ 3
canonicalBTBoundaryCrossSectionRowCountIs3 =
  refl

p2BoundaryCrossSectionCardinalityIs3 :
  crossSectionCardinality p2BoundaryCrossSectionRow ≡ 3
p2BoundaryCrossSectionCardinalityIs3 =
  refl

p3BoundaryCrossSectionCardinalityIs4 :
  crossSectionCardinality p3BoundaryCrossSectionRow ≡ 4
p3BoundaryCrossSectionCardinalityIs4 =
  refl

p7BoundaryCrossSectionCardinalityIs8 :
  crossSectionCardinality p7BoundaryCrossSectionRow ≡ 8
p7BoundaryCrossSectionCardinalityIs8 =
  refl

p2BoundarySmoothS2NotPromoted :
  smoothS2BoundaryPromoted p2BoundaryCrossSectionRow ≡ false
p2BoundarySmoothS2NotPromoted =
  refl

p3BoundarySmoothS2NotPromoted :
  smoothS2BoundaryPromoted p3BoundaryCrossSectionRow ≡ false
p3BoundarySmoothS2NotPromoted =
  refl

p7BoundarySmoothS2NotPromoted :
  smoothS2BoundaryPromoted p7BoundaryCrossSectionRow ≡ false
p7BoundarySmoothS2NotPromoted =
  refl

p2BoundaryNotArchimedeanS2 :
  archimedeanS2Identification p2BoundaryCrossSectionRow ≡ false
p2BoundaryNotArchimedeanS2 =
  refl

p3BoundaryNotArchimedeanS2 :
  archimedeanS2Identification p3BoundaryCrossSectionRow ≡ false
p3BoundaryNotArchimedeanS2 =
  refl

p7BoundaryNotArchimedeanS2 :
  archimedeanS2Identification p7BoundaryCrossSectionRow ≡ false
p7BoundaryNotArchimedeanS2 =
  refl
