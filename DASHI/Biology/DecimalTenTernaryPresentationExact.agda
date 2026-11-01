module DASHI.Biology.DecimalTenTernaryPresentationExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Biology.PointedTernaryBulkExact as Pointed
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Symmetry

------------------------------------------------------------------------
-- Three exact ten-element presentations appearing in the discussion:
--
--   10 = decimal digits,
--   10 = 1 unmarked + 9 marked sites,
--   10 = 5 D4 irrep species x 2 orientations.
--
-- Equal cardinality does not identify their semantics, group actions, or
-- physical roles.  In particular the 5 x 2 carrier includes the A2 role as an
-- oriented refinement even though A2 has multiplicity zero in the raw nine-site
-- permutation representation.
------------------------------------------------------------------------

DecimalDigit : Set
DecimalDigit = Fin 10

PointedMarkerTen : Set
PointedMarkerTen = Pointed.MarkedOrUnmarkedSite

IrrepOrientationTen : Set
IrrepOrientationTen =
  Symmetry.D4IrrepKind × Symmetry.DialecticalOrientation

decimalDigitCount : Nat
decimalDigitCount = 10

pointedMarkerCount : Nat
pointedMarkerCount = Pointed.markerCount

irrepSpeciesCount : Nat
irrepSpeciesCount = 5

orientationCount : Nat
orientationCount = 2

irrepOrientationCount : Nat
irrepOrientationCount = irrepSpeciesCount * orientationCount

pointedMarkerCountIsTen : pointedMarkerCount ≡ 10
pointedMarkerCountIsTen = Pointed.markerCountIsTen

irrepOrientationCountIsTen : irrepOrientationCount ≡ 10
irrepOrientationCountIsTen = refl

decimalPointedAndIrrepCountsAgree :
  decimalDigitCount ≡ pointedMarkerCount
  × pointedMarkerCount ≡ irrepOrientationCount
decimalPointedAndIrrepCountsAgree = refl , refl

------------------------------------------------------------------------
-- The existing explicit list witnesses the 5 x 2 presentation.  It remains a
-- sector-role atlas, not the isotypic decomposition of the raw nine-site action.
------------------------------------------------------------------------

irrepOrientationSectors : List Symmetry.SymmetrySector
irrepOrientationSectors = Symmetry.canonicalTenSectors

irrepOrientationSectorCount : Nat
irrepOrientationSectorCount = Symmetry.listCount irrepOrientationSectors

irrepOrientationSectorCountIsTen :
  irrepOrientationSectorCount ≡ 10
irrepOrientationSectorCountIsTen = Symmetry.sectorCountIsTen

rawNineA2MultiplicityIsZero :
  Symmetry.rawNineMultiplicity Symmetry.A2 ≡ 0
rawNineA2MultiplicityIsZero = Symmetry.rawA2MultiplicityIsZero

------------------------------------------------------------------------
-- Explicit bridge obligations.  A bare bijection would transport ten labels,
-- but a meaningful reuse also needs the relevant action or observer to commute.
------------------------------------------------------------------------

record TenCarrierEquivalence (A B : Set) : Set where
  constructor tenCarrierEquivalence
  field
    encode : A → B
    decode : B → A
    decodeEncode : (x : A) → decode (encode x) ≡ x
    encodeDecode : (y : B) → encode (decode y) ≡ y

record PointedIrrepObserverBridge : Set where
  constructor pointedIrrepObserverBridge
  field
    carrierEquivalence :
      TenCarrierEquivalence PointedMarkerTen IrrepOrientationTen

    rotationObserverCommutes : Bool
    rotationObserverCommutesIsTrue :
      rotationObserverCommutes ≡ true

    reflectionObserverCommutes : Bool
    reflectionObserverCommutesIsTrue :
      reflectionObserverCommutes ≡ true

    A2RefinementSourceDeclared : Bool
    A2RefinementSourceDeclaredIsTrue :
      A2RefinementSourceDeclared ≡ true

------------------------------------------------------------------------
-- Decimal outer product with the existing ternary sheet count.
------------------------------------------------------------------------

decimalTernaryBulkDimension : Nat
decimalTernaryBulkDimension =
  decimalDigitCount * Pointed.ternarySheetCount

decimalTernaryBulkDimensionIs196830 :
  decimalTernaryBulkDimension ≡ 196830
decimalTernaryBulkDimensionIs196830 = refl

decimalAndPointedBulkDimensionsAgree :
  decimalTernaryBulkDimension ≡ Pointed.pointedBulkDimension
decimalAndPointedBulkDimensionsAgree = refl

record DecimalTenTernaryPresentationBoundary : Set where
  constructor decimalTenTernaryPresentationBoundary
  field
    equalCardinalityIdentifiesPresentations : Bool
    equalCardinalityIdentifiesPresentationsIsFalse :
      equalCardinalityIdentifiesPresentations ≡ false

    fiveIrrepSpeciesMeansRawCarrierContainsA2 : Bool
    fiveIrrepSpeciesMeansRawCarrierContainsA2IsFalse :
      fiveIrrepSpeciesMeansRawCarrierContainsA2 ≡ false

    tenSectorListIsRawD4IsotypicDecomposition : Bool
    tenSectorListIsRawD4IsotypicDecompositionIsFalse :
      tenSectorListIsRawD4IsotypicDecomposition ≡ false

    baseTenNotationConstructsMonsterAction : Bool
    baseTenNotationConstructsMonsterActionIsFalse :
      baseTenNotationConstructsMonsterAction ≡ false

    pointedAndIrrepPresentationsCanBeComparedByBridge : Bool
    pointedAndIrrepPresentationsCanBeComparedByBridgeIsTrue :
      pointedAndIrrepPresentationsCanBeComparedByBridge ≡ true

open DecimalTenTernaryPresentationBoundary public

canonicalDecimalTenTernaryPresentationBoundary :
  DecimalTenTernaryPresentationBoundary
canonicalDecimalTenTernaryPresentationBoundary =
  decimalTenTernaryPresentationBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
