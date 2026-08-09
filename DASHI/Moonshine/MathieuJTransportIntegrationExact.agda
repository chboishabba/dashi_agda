module DASHI.Moonshine.MathieuJTransportIntegrationExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Integrate the corrected indexed external-point gluing with the exact
-- Mathieu order/index spine.  The same numbers 9, 10 and 11 occur in two
-- typed layers:
--
--   pointed sets:  10 = 9 + 1, 11 = 10 + 1;
--   group orders:  720 = 10 * 72, 7920 = 11 * 720.
--
-- The module keeps those layers related but non-identical.  It supplies a
-- finite model of external point -> transported representative -> joined
-- coordinate without identifying the point with the classical modular j.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IndexedJExternalGluingExact as Gluing
import DASHI.Moonshine.MathieuStabilizerTowerExact as Mathieu

pointedTenCount : Nat
pointedTenCount = 9 + 1

pointedElevenCount : Nat
pointedElevenCount = pointedTenCount + 1

pointedTenCountIsTen : pointedTenCount ≡ 10
pointedTenCountIsTen = refl

pointedElevenCountIsEleven : pointedElevenCount ≡ 11
pointedElevenCountIsEleven = refl

mathieuTenOrbitOrderLaw :
  Mathieu.levelOrder Mathieu.M10Level
  ≡ pointedTenCount * Mathieu.levelOrder Mathieu.M9Level
mathieuTenOrbitOrderLaw = refl

mathieuElevenOrbitOrderLaw :
  Mathieu.levelOrder Mathieu.M11Level
  ≡ pointedElevenCount * Mathieu.levelOrder Mathieu.M10Level
mathieuElevenOrbitOrderLaw = refl

record IndexedTransportStage : Set where
  constructor indexedTransportStage
  field
    hostWidth : Nat
    localGuestIndex : Nat
    transportedGuestIndex : Nat
    transportIndexLaw : transportedGuestIndex ≡ localGuestIndex + hostWidth

open IndexedTransportStage public

canonicalNineHostTransport : IndexedTransportStage
canonicalNineHostTransport = indexedTransportStage 9 1 10 refl

canonicalTransportMatchesGluing :
  transportedGuestIndex canonicalNineHostTransport
  ≡ Gluing.representationIndex Gluing.transportedTen
canonicalTransportMatchesGluing = refl

canonicalLocalMatchesGluing :
  localGuestIndex canonicalNineHostTransport
  ≡ Gluing.representationIndex Gluing.localOne
canonicalLocalMatchesGluing = refl

record JoinedTransportStage : Set where
  constructor joinedTransportStage
  field
    intrinsicIndex : Nat
    transportedIndex : Nat
    totalIndex : Nat
    joinedIndexLaw : totalIndex ≡ intrinsicIndex + transportedIndex

open JoinedTransportStage public

canonicalJoinedStage : JoinedTransportStage
canonicalJoinedStage = joinedTransportStage 1 10 11 refl

canonicalJoinedStageMatchesGluing :
  totalIndex canonicalJoinedStage ≡ Gluing.joinedAddressIndex
canonicalJoinedStageMatchesGluing = refl

record StabilizerTransportAnalogy : Set where
  constructor stabilizerTransportAnalogy
  field
    internalCarrierOrder : Nat
    completedCarrierOrder : Nat
    pointOrbitSize : Nat
    transformationOrderLaw :
      completedCarrierOrder ≡ pointOrbitSize * internalCarrierOrder
    hostPointCount : Nat
    adjoinedPointCount : Nat
    completedPointCount : Nat
    pointCountLaw :
      completedPointCount ≡ hostPointCount + adjoinedPointCount

open StabilizerTransportAnalogy public

canonicalNineToTenAnalogy : StabilizerTransportAnalogy
canonicalNineToTenAnalogy =
  stabilizerTransportAnalogy
    72 720 10 refl
    9 1 10 refl

canonicalTenToElevenAnalogy : StabilizerTransportAnalogy
canonicalTenToElevenAnalogy =
  stabilizerTransportAnalogy
    720 7920 11 refl
    10 1 11 refl

record MathieuJGluingBoundary : Set where
  constructor mathieuJGluingBoundary
  field
    pointCountAdditionEqualsGroupOrderMultiplication : Bool
    pointCountAdditionEqualsGroupOrderMultiplicationIsFalse :
      pointCountAdditionEqualsGroupOrderMultiplication ≡ false
    sameOrbitNumberLinksTheTwoTypedLayers : Bool
    sameOrbitNumberLinksTheTwoTypedLayersIsTrue :
      sameOrbitNumberLinksTheTwoTypedLayers ≡ true
    actualMathieuCosetActionConstructedHere : Bool
    actualMathieuCosetActionConstructedHereIsFalse :
      actualMathieuCosetActionConstructedHere ≡ false
    transportedGuestIsClassicalModularJ : Bool
    transportedGuestIsClassicalModularJIsFalse :
      transportedGuestIsClassicalModularJ ≡ false
    arithmeticAnalogyProvesMonsterMoonshine : Bool
    arithmeticAnalogyProvesMonsterMoonshineIsFalse :
      arithmeticAnalogyProvesMonsterMoonshine ≡ false

canonicalMathieuJGluingBoundary : MathieuJGluingBoundary
canonicalMathieuJGluingBoundary =
  mathieuJGluingBoundary false refl true refl false refl false refl false refl
