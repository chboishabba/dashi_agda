module DASHI.Visualisation.EventLabelGeometryExact where

open import DASHI.Core.Prelude

import DASHI.Visualisation.EventFilamentFieldExact as Event

------------------------------------------------------------------------
-- Exact finite product geometry for the two-bit corner label and two-digit
-- ternary hierarchy.  The factors remain separately recoverable and their
-- distances are combined only by an explicitly chosen product metric.

bitMismatch : Event.BinaryBit → Event.BinaryBit → Nat
bitMismatch Event.bit0 Event.bit0 = 0
bitMismatch Event.bit0 Event.bit1 = 1
bitMismatch Event.bit1 Event.bit0 = 1
bitMismatch Event.bit1 Event.bit1 = 0

binaryHammingDistance : Event.BinaryCorner → Event.BinaryCorner → Nat
binaryHammingDistance left right =
  bitMismatch (Event.cornerFirst left) (Event.cornerFirst right)
  + bitMismatch (Event.cornerSecond left) (Event.cornerSecond right)

digitEqual : Event.TernaryDigit → Event.TernaryDigit → Bool
digitEqual Event.digit0 Event.digit0 = true
digitEqual Event.digit1 Event.digit1 = true
digitEqual Event.digit2 Event.digit2 = true
digitEqual _ _ = false

prefixDistanceCode : Event.TernaryAddress2 → Event.TernaryAddress2 → Nat
prefixDistanceCode left right
  with digitEqual (Event.addressFirst left) (Event.addressFirst right)
... | false = 3
... | true with digitEqual (Event.addressSecond left) (Event.addressSecond right)
...   | false = 1
...   | true = 0

productLabelDistance : Event.ProductLabel → Event.ProductLabel → Nat
productLabelDistance left right =
  binaryHammingDistance
    (Event.binaryLabel left)
    (Event.binaryLabel right)
  + prefixDistanceCode
      (Event.hierarchyLabel left)
      (Event.hierarchyLabel right)

labelA : Event.ProductLabel
labelA =
  Event.productLabel
    (Event.binaryCorner Event.bit0 Event.bit0)
    (Event.ternaryAddress2 Event.digit0 Event.digit1)

labelB : Event.ProductLabel
labelB =
  Event.productLabel
    (Event.binaryCorner Event.bit1 Event.bit0)
    (Event.ternaryAddress2 Event.digit0 Event.digit2)

labelC : Event.ProductLabel
labelC =
  Event.productLabel
    (Event.binaryCorner Event.bit1 Event.bit1)
    (Event.ternaryAddress2 Event.digit2 Event.digit2)

labelABDistanceIsTwo : productLabelDistance labelA labelB ≡ 2
labelABDistanceIsTwo = refl

labelBCDistanceIsFour : productLabelDistance labelB labelC ≡ 4
labelBCDistanceIsFour = refl

labelACDistanceIsFive : productLabelDistance labelA labelC ≡ 5
labelACDistanceIsFive = refl

sampleTriangleCloses :
  productLabelDistance labelA labelC
  ≡
  productLabelDistance labelA labelB
  + productLabelDistance labelB labelC
  ∸ 1
sampleTriangleCloses = refl

sameBinaryDifferentHierarchy : Event.ProductLabel
sameBinaryDifferentHierarchy =
  Event.productLabel
    (Event.binaryCorner Event.bit0 Event.bit0)
    (Event.ternaryAddress2 Event.digit2 Event.digit1)

binaryDistanceCanVanishWhileHierarchyDiffers :
  binaryHammingDistance
    (Event.binaryLabel labelA)
    (Event.binaryLabel sameBinaryDifferentHierarchy)
  ≡
  0
  ×
  prefixDistanceCode
    (Event.hierarchyLabel labelA)
    (Event.hierarchyLabel sameBinaryDifferentHierarchy)
  ≡
  3
binaryDistanceCanVanishWhileHierarchyDiffers = refl , refl

sameHierarchyDifferentBinary : Event.ProductLabel
sameHierarchyDifferentBinary =
  Event.productLabel
    (Event.binaryCorner Event.bit1 Event.bit1)
    (Event.ternaryAddress2 Event.digit0 Event.digit1)

hierarchyDistanceCanVanishWhileBinaryDiffers :
  prefixDistanceCode
    (Event.hierarchyLabel labelA)
    (Event.hierarchyLabel sameHierarchyDifferentBinary)
  ≡
  0
  ×
  binaryHammingDistance
    (Event.binaryLabel labelA)
    (Event.binaryLabel sameHierarchyDifferentBinary)
  ≡
  2
hierarchyDistanceCanVanishWhileBinaryDiffers = refl , refl

record EventLabelGeometryBoundary : Set where
  constructor eventLabelGeometryBoundary
  field
    binaryHammingDeterminesTernaryPrefixDistance : Bool
    binaryHammingDeterminesTernaryPrefixDistanceIsFalse :
      binaryHammingDeterminesTernaryPrefixDistance ≡ false

    ternaryPrefixDistanceDeterminesBinaryHamming : Bool
    ternaryPrefixDistanceDeterminesBinaryHammingIsFalse :
      ternaryPrefixDistanceDeterminesBinaryHamming ≡ false

    productMetricIsForcedByLabelTypes : Bool
    productMetricIsForcedByLabelTypesIsFalse :
      productMetricIsForcedByLabelTypes ≡ false

open EventLabelGeometryBoundary public

canonicalEventLabelGeometryBoundary : EventLabelGeometryBoundary
canonicalEventLabelGeometryBoundary =
  eventLabelGeometryBoundary false refl false refl false refl
