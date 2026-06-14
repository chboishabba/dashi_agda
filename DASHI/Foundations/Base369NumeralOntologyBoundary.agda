module DASHI.Foundations.Base369NumeralOntologyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import Base369 as Base
import DASHI.Foundations.Base369FiniteRingLaws as Laws

------------------------------------------------------------------------
-- Role tags and no-confusion receipts.

data Empty : Set where

data NumeralOntologyRoleTag : Set where
  algebraicCarrierRoleTag :
    NumeralOntologyRoleTag

  primeCoordinateBoundaryRoleTag :
    NumeralOntologyRoleTag

  uftTraversalAddressRoleTag :
    NumeralOntologyRoleTag

algebraicCarrier≠primeCoordinate :
  algebraicCarrierRoleTag ≡ primeCoordinateBoundaryRoleTag →
  Empty
algebraicCarrier≠primeCoordinate ()

algebraicCarrier≠uftTraversalAddress :
  algebraicCarrierRoleTag ≡ uftTraversalAddressRoleTag →
  Empty
algebraicCarrier≠uftTraversalAddress ()

primeCoordinate≠uftTraversalAddress :
  primeCoordinateBoundaryRoleTag ≡ uftTraversalAddressRoleTag →
  Empty
primeCoordinate≠uftTraversalAddress ()

------------------------------------------------------------------------
-- Local low-dependency boundary carriers.

record PrimeCoordinate15Tuple (A : Set) : Set where
  constructor primeCoordinate15Tuple
  field
    e2 e3 e5 e7 e11 :
      A

    e13 e17 e19 e23 e29 :
      A

    e31 e41 e47 e59 e71 :
      A

open PrimeCoordinate15Tuple public

data PrimeCoordinate15 : Set where
  p2-coordinate :
    PrimeCoordinate15

  p3-coordinate :
    PrimeCoordinate15

  p5-coordinate :
    PrimeCoordinate15

  p7-coordinate :
    PrimeCoordinate15

  p11-coordinate :
    PrimeCoordinate15

  p13-coordinate :
    PrimeCoordinate15

  p17-coordinate :
    PrimeCoordinate15

  p19-coordinate :
    PrimeCoordinate15

  p23-coordinate :
    PrimeCoordinate15

  p29-coordinate :
    PrimeCoordinate15

  p31-coordinate :
    PrimeCoordinate15

  p41-coordinate :
    PrimeCoordinate15

  p47-coordinate :
    PrimeCoordinate15

  p59-coordinate :
    PrimeCoordinate15

  p71-coordinate :
    PrimeCoordinate15

FactorVec15Boundary :
  Set
FactorVec15Boundary =
  PrimeCoordinate15Tuple Nat

canonicalPrimeCoordinate15Tuple :
  PrimeCoordinate15Tuple PrimeCoordinate15
canonicalPrimeCoordinate15Tuple =
  primeCoordinate15Tuple
    p2-coordinate
    p3-coordinate
    p5-coordinate
    p7-coordinate
    p11-coordinate
    p13-coordinate
    p17-coordinate
    p19-coordinate
    p23-coordinate
    p29-coordinate
    p31-coordinate
    p41-coordinate
    p47-coordinate
    p59-coordinate
    p71-coordinate

data UFTTraversalAddress : Set where
  normalUFTTraversalAddress :
    Nat →
    UFTTraversalAddress

  specialUFTTraversalAddress :
    Nat →
    UFTTraversalAddress

------------------------------------------------------------------------
-- Non-promoting narrative carrier.

record NonPromotingNarrativeClaim : Set where
  field
    claimText :
      String

    promotesFormalResult :
      Bool

    promotesFormalResult-is-false :
      promotesFormalResult ≡ false

open NonPromotingNarrativeClaim public

mkNonPromotingNarrativeClaim :
  String →
  NonPromotingNarrativeClaim
mkNonPromotingNarrativeClaim text =
  record
    { claimText = text
    ; promotesFormalResult = false
    ; promotesFormalResult-is-false = refl
    }

------------------------------------------------------------------------
-- Role 1: algebraic carrier.
--
-- These fields consume the checked Base369 finite ring/algebra surfaces.

record AlgebraicCarrierRole : Set₁ where
  field
    triCarrier :
      Set

    triCarrier-is-Base369-TriTruth :
      triCarrier ≡ Base.TriTruth

    triFieldReceipt :
      Laws.TriTruthIsField

    triAddZeroLReceipt :
      (x : Base.TriTruth) →
      Base.triXor Base.tri-low x ≡ x

    triMulOneLReceipt :
      (x : Base.TriTruth) →
      Laws.triTruthMul Base.tri-mid x ≡ x

    hexCarrier :
      Set

    hexCarrier-is-Base369-HexTruth :
      hexCarrier ≡ Base.HexTruth

    hexRingAuthority :
      Laws.RingAuthoritySlot

    hexZeroDivisorReceipt :
      Laws.ZeroDivisorWitness Base.HexTruth Base.hex-0 Laws.hexTruthMul

    nonaryCarrier :
      Set

    nonaryCarrier-is-Base369-NonaryTruth :
      nonaryCarrier ≡ Base.NonaryTruth

    nonaryRingAuthority :
      Laws.RingAuthoritySlot

    nonaryZeroDivisorReceipt :
      Laws.ZeroDivisorWitness Base.NonaryTruth Base.non-0 Laws.nonaryTruthMul

open AlgebraicCarrierRole public

base369AlgebraicCarrierRole :
  AlgebraicCarrierRole
base369AlgebraicCarrierRole =
  record
    { triCarrier = Base.TriTruth
    ; triCarrier-is-Base369-TriTruth = refl
    ; triFieldReceipt = Laws.triTruthFieldReceipt
    ; triAddZeroLReceipt =
        Laws.TriTruthRingLaws.addZeroL Laws.triTruthRingLaws
    ; triMulOneLReceipt =
        Laws.TriTruthRingLaws.mulOneL Laws.triTruthRingLaws
    ; hexCarrier = Base.HexTruth
    ; hexCarrier-is-Base369-HexTruth = refl
    ; hexRingAuthority = Laws.hexTruthRingAuthoritySlot
    ; hexZeroDivisorReceipt = Laws.hexZeroDivisorWitness
    ; nonaryCarrier = Base.NonaryTruth
    ; nonaryCarrier-is-Base369-NonaryTruth = refl
    ; nonaryRingAuthority = Laws.nonaryTruthRingAuthoritySlot
    ; nonaryZeroDivisorReceipt =
        Laws.nonaryZeroDivisorWitness-3-3
    }

------------------------------------------------------------------------
-- Role 2: 15-prime coordinate boundary.

record PrimeCoordinateBoundaryRole : Set₁ where
  field
    coordinateCarrier :
      Set

    coordinateCarrier-is-FactorVec15Boundary :
      coordinateCarrier ≡ FactorVec15Boundary

    coordinateShape :
      Set

    coordinateShape-is-PrimeCoordinate15Tuple-Nat :
      coordinateShape ≡ PrimeCoordinate15Tuple Nat

    trackedPrimeCoordinates :
      PrimeCoordinate15Tuple PrimeCoordinate15

    trackedPrimeCoordinates-is-canonical :
      trackedPrimeCoordinates ≡ canonicalPrimeCoordinate15Tuple

    trackedPrimeCoordinateCount :
      Nat

    trackedPrimeCoordinateCount-is-15 :
      trackedPrimeCoordinateCount ≡ 15

    coordinateBoundaryPromotesAlgebraCarrier :
      Bool

    coordinateBoundaryPromotesAlgebraCarrier-is-false :
      coordinateBoundaryPromotesAlgebraCarrier ≡ false

    coordinateBoundaryNarrative :
      NonPromotingNarrativeClaim

open PrimeCoordinateBoundaryRole public

base369PrimeCoordinateBoundaryRole :
  PrimeCoordinateBoundaryRole
base369PrimeCoordinateBoundaryRole =
  record
    { coordinateCarrier = FactorVec15Boundary
    ; coordinateCarrier-is-FactorVec15Boundary = refl
    ; coordinateShape = PrimeCoordinate15Tuple Nat
    ; coordinateShape-is-PrimeCoordinate15Tuple-Nat = refl
    ; trackedPrimeCoordinates = canonicalPrimeCoordinate15Tuple
    ; trackedPrimeCoordinates-is-canonical = refl
    ; trackedPrimeCoordinateCount = 15
    ; trackedPrimeCoordinateCount-is-15 = refl
    ; coordinateBoundaryPromotesAlgebraCarrier = false
    ; coordinateBoundaryPromotesAlgebraCarrier-is-false = refl
    ; coordinateBoundaryNarrative =
        mkNonPromotingNarrativeClaim
          "The 15-prime Vec15/FactorVec surface is a coordinate boundary, not the Base369 algebraic carrier."
    }

------------------------------------------------------------------------
-- Role 3: UFT/UFTC traversal address boundary.

record UFTTraversalAddressRole : Set₁ where
  field
    addressCarrier :
      Set

    addressCarrier-is-UFTTraversalAddress :
      addressCarrier ≡ UFTTraversalAddress

    severityCarrier :
      Set

    severityCarrier-is-Nat :
      severityCarrier ≡ Nat

    normalTraversalAddress :
      UFTTraversalAddress

    traversalJoin :
      UFTTraversalAddress →
      UFTTraversalAddress →
      UFTTraversalAddress

    traversalAddressPromotesAlgebraCarrier :
      Bool

    traversalAddressPromotesAlgebraCarrier-is-false :
      traversalAddressPromotesAlgebraCarrier ≡ false

    traversalAddressNarrative :
      NonPromotingNarrativeClaim

open UFTTraversalAddressRole public

boundaryTraversalJoin :
  UFTTraversalAddress →
  UFTTraversalAddress →
  UFTTraversalAddress
boundaryTraversalJoin (normalUFTTraversalAddress n) _ =
  normalUFTTraversalAddress n
boundaryTraversalJoin (specialUFTTraversalAddress n) _ =
  specialUFTTraversalAddress n

base369UFTTraversalAddressRole :
  UFTTraversalAddressRole
base369UFTTraversalAddressRole =
  record
    { addressCarrier = UFTTraversalAddress
    ; addressCarrier-is-UFTTraversalAddress = refl
    ; severityCarrier = Nat
    ; severityCarrier-is-Nat = refl
    ; normalTraversalAddress = normalUFTTraversalAddress 0
    ; traversalJoin = boundaryTraversalJoin
    ; traversalAddressPromotesAlgebraCarrier = false
    ; traversalAddressPromotesAlgebraCarrier-is-false = refl
    ; traversalAddressNarrative =
        mkNonPromotingNarrativeClaim
          "The UFT/UFTC traversal code is an address/control surface, not the Base369 algebraic carrier and not the 15-prime coordinate boundary."
    }

------------------------------------------------------------------------
-- Boundary package: the three roles are present and non-conflated.

record Base369NumeralOntologyBoundary : Set₁ where
  field
    algebraicCarrier :
      AlgebraicCarrierRole

    primeCoordinateBoundary :
      PrimeCoordinateBoundaryRole

    uftTraversalAddress :
      UFTTraversalAddressRole

    algebraicCarrierTag :
      NumeralOntologyRoleTag

    algebraicCarrierTag-is-canonical :
      algebraicCarrierTag ≡ algebraicCarrierRoleTag

    primeCoordinateBoundaryTag :
      NumeralOntologyRoleTag

    primeCoordinateBoundaryTag-is-canonical :
      primeCoordinateBoundaryTag ≡ primeCoordinateBoundaryRoleTag

    uftTraversalAddressTag :
      NumeralOntologyRoleTag

    uftTraversalAddressTag-is-canonical :
      uftTraversalAddressTag ≡ uftTraversalAddressRoleTag

    algebraicCarrierTagNotPrimeCoordinateTag :
      algebraicCarrierRoleTag ≡ primeCoordinateBoundaryRoleTag →
      Empty

    algebraicCarrierTagNotUFTTraversalAddressTag :
      algebraicCarrierRoleTag ≡ uftTraversalAddressRoleTag →
      Empty

    primeCoordinateTagNotUFTTraversalAddressTag :
      primeCoordinateBoundaryRoleTag ≡ uftTraversalAddressRoleTag →
      Empty

    boundaryNarrative :
      NonPromotingNarrativeClaim

open Base369NumeralOntologyBoundary public

canonicalBase369NumeralOntologyBoundary :
  Base369NumeralOntologyBoundary
canonicalBase369NumeralOntologyBoundary =
  record
    { algebraicCarrier =
        base369AlgebraicCarrierRole
    ; primeCoordinateBoundary =
        base369PrimeCoordinateBoundaryRole
    ; uftTraversalAddress =
        base369UFTTraversalAddressRole
    ; algebraicCarrierTag =
        algebraicCarrierRoleTag
    ; algebraicCarrierTag-is-canonical =
        refl
    ; primeCoordinateBoundaryTag =
        primeCoordinateBoundaryRoleTag
    ; primeCoordinateBoundaryTag-is-canonical =
        refl
    ; uftTraversalAddressTag =
        uftTraversalAddressRoleTag
    ; uftTraversalAddressTag-is-canonical =
        refl
    ; algebraicCarrierTagNotPrimeCoordinateTag =
        algebraicCarrier≠primeCoordinate
    ; algebraicCarrierTagNotUFTTraversalAddressTag =
        algebraicCarrier≠uftTraversalAddress
    ; primeCoordinateTagNotUFTTraversalAddressTag =
        primeCoordinate≠uftTraversalAddress
    ; boundaryNarrative =
        mkNonPromotingNarrativeClaim
          "Base369 numeral ontology boundary: algebraic carrier, 15-prime coordinate boundary, and UFT traversal address are recorded as separate roles; only imported algebra receipts promote formal facts."
    }
