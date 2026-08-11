module DASHI.Biology.IndexedJExternalGluingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", second edition,
-- Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- DASHI CONTRIBUTION
--
-- Formalize the corrected 0 ~ 1 ~ 10 ~ 11 reading as a typed change of
-- indexing convention followed by attachment of an external pointed object.
-- The external point has a local representative 1_J and a transported
-- representative 10_{J/F}; both project to the same seam of a zero-indexed
-- nine-ring.  The joined address 11 retains one intrinsic fibre coordinate
-- together with the transported external coordinate.
--
-- The finite construction below is an explicit pushout-shaped attachment.
-- It does not claim a universal property in an ambient category and does not
-- identify the external point with the classical modular j-invariant.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- The intrinsic zero-indexed nine-ring and its one-indexed linear lift.
------------------------------------------------------------------------

data NineRing0 : Set where
  r0 r1 r2 r3 r4 r5 r6 r7 r8 : NineRing0

data LinearTen : Set where
  l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : LinearTen

zeroIndexedToOneIndexed : NineRing0 → LinearTen
zeroIndexedToOneIndexed r0 = l1
zeroIndexedToOneIndexed r1 = l2
zeroIndexedToOneIndexed r2 = l3
zeroIndexedToOneIndexed r3 = l4
zeroIndexedToOneIndexed r4 = l5
zeroIndexedToOneIndexed r5 = l6
zeroIndexedToOneIndexed r6 = l7
zeroIndexedToOneIndexed r7 = l8
zeroIndexedToOneIndexed r8 = l9

closeLinearTen : LinearTen → NineRing0
closeLinearTen l1 = r0
closeLinearTen l2 = r1
closeLinearTen l3 = r2
closeLinearTen l4 = r3
closeLinearTen l5 = r4
closeLinearTen l6 = r5
closeLinearTen l7 = r6
closeLinearTen l8 = r7
closeLinearTen l9 = r8
closeLinearTen l10 = r0

oneIndexedForgetsToZero :
  (point : NineRing0) →
  closeLinearTen (zeroIndexedToOneIndexed point) ≡ point
oneIndexedForgetsToZero r0 = refl
oneIndexedForgetsToZero r1 = refl
oneIndexedForgetsToZero r2 = refl
oneIndexedForgetsToZero r3 = refl
oneIndexedForgetsToZero r4 = refl
oneIndexedForgetsToZero r5 = refl
oneIndexedForgetsToZero r6 = refl
oneIndexedForgetsToZero r7 = refl
oneIndexedForgetsToZero r8 = refl

zeroAndOneShareSeam : closeLinearTen l1 ≡ r0
zeroAndOneShareSeam = refl

oneAndTenCloseToSameSeam : closeLinearTen l1 ≡ closeLinearTen l10
oneAndTenCloseToSameSeam = refl

------------------------------------------------------------------------
-- A generic pointed attachment interface and one concrete finite instance.
------------------------------------------------------------------------

record PointedAttachment (F J : Set) : Set₁ where
  field
    Glued : Set
    fibreBase : F
    externalBase : J
    includeFibre : F → Glued
    includeExternal : J → Glued
    seam : includeFibre fibreBase ≡ includeExternal externalBase

open PointedAttachment public

data ExternalJ : Set where
  jOne : ExternalJ

data GluedNineWithJ : Set where
  seamPoint : GluedNineWithJ
  host1 host2 host3 host4 host5 host6 host7 host8 : GluedNineWithJ

includeNine : NineRing0 → GluedNineWithJ
includeNine r0 = seamPoint
includeNine r1 = host1
includeNine r2 = host2
includeNine r3 = host3
includeNine r4 = host4
includeNine r5 = host5
includeNine r6 = host6
includeNine r7 = host7
includeNine r8 = host8

includeJ : ExternalJ → GluedNineWithJ
includeJ jOne = seamPoint

canonicalPointedAttachment : PointedAttachment NineRing0 ExternalJ
canonicalPointedAttachment = record
  { Glued = GluedNineWithJ
  ; fibreBase = r0
  ; externalBase = jOne
  ; includeFibre = includeNine
  ; includeExternal = includeJ
  ; seam = refl
  }

canonicalZeroOneSeam :
  includeFibre canonicalPointedAttachment r0
  ≡ includeExternal canonicalPointedAttachment jOne
canonicalZeroOneSeam = seam canonicalPointedAttachment

------------------------------------------------------------------------
-- The external point before and after transport through the host chart.
------------------------------------------------------------------------

data JRepresentation : Set where
  localOne transportedTen : JRepresentation

forgetJRepresentation : JRepresentation → ExternalJ
forgetJRepresentation localOne = jOne
forgetJRepresentation transportedTen = jOne

localAndTransportedRepresentSameExternalPoint :
  forgetJRepresentation localOne
  ≡ forgetJRepresentation transportedTen
localAndTransportedRepresentSameExternalPoint = refl

representationIndex : JRepresentation → Nat
representationIndex localOne = 1
representationIndex transportedTen = 10

hostTransportWidth : Nat
hostTransportWidth = 9

transportedIndexLaw :
  representationIndex transportedTen
  ≡ representationIndex localOne + hostTransportWidth
transportedIndexLaw = refl

projectJRepresentationToSeam : JRepresentation → NineRing0
projectJRepresentationToSeam localOne = r0
projectJRepresentationToSeam transportedTen = r0

transportProjectionForgetsHostDisplacement :
  projectJRepresentationToSeam localOne
  ≡ projectJRepresentationToSeam transportedTen
transportProjectionForgetsHostDisplacement = refl

------------------------------------------------------------------------
-- 11 retains both an intrinsic coordinate and the transported guest.
------------------------------------------------------------------------

record JoinedCoordinate : Set where
  constructor joinedCoordinate
  field
    intrinsicCoordinate : NineRing0
    externalCoordinate : JRepresentation

open JoinedCoordinate public

canonicalJoinedEleven : JoinedCoordinate
canonicalJoinedEleven = joinedCoordinate r1 transportedTen

intrinsicLocalIndex : Nat
intrinsicLocalIndex = 1

transportedExternalIndex : Nat
transportedExternalIndex = representationIndex transportedTen

joinedAddressIndex : Nat
joinedAddressIndex = intrinsicLocalIndex + transportedExternalIndex

joinedAddressIndexIsEleven : joinedAddressIndex ≡ 11
joinedAddressIndexIsEleven = refl

canonicalJoinRetainsIntrinsicOne :
  intrinsicCoordinate canonicalJoinedEleven ≡ r1
canonicalJoinRetainsIntrinsicOne = refl

canonicalJoinRetainsTransportedTen :
  externalCoordinate canonicalJoinedEleven ≡ transportedTen
canonicalJoinRetainsTransportedTen = refl

------------------------------------------------------------------------
-- Epistemic boundary.
------------------------------------------------------------------------

record IndexedJGluingBoundary : Set where
  constructor indexedJGluingBoundary
  field
    zeroAndOneAreOrdinaryNaturalEquality : Bool
    zeroAndOneAreOrdinaryNaturalEqualityIsFalse :
      zeroAndOneAreOrdinaryNaturalEquality ≡ false
    oneAndTenAreTwoRepresentativesOfOneExternalPoint : Bool
    oneAndTenAreTwoRepresentativesOfOneExternalPointIsTrue :
      oneAndTenAreTwoRepresentativesOfOneExternalPoint ≡ true
    elevenRetainsHostAndGuestCoordinates : Bool
    elevenRetainsHostAndGuestCoordinatesIsTrue :
      elevenRetainsHostAndGuestCoordinates ≡ true
    finiteAttachmentProvesCategoricalPushoutUniversalProperty : Bool
    finiteAttachmentProvesCategoricalPushoutUniversalPropertyIsFalse :
      finiteAttachmentProvesCategoricalPushoutUniversalProperty ≡ false
    externalJIsClassicalModularInvariant : Bool
    externalJIsClassicalModularInvariantIsFalse :
      externalJIsClassicalModularInvariant ≡ false

canonicalIndexedJGluingBoundary : IndexedJGluingBoundary
canonicalIndexedJGluingBoundary =
  indexedJGluingBoundary false refl true refl true refl false refl false refl
