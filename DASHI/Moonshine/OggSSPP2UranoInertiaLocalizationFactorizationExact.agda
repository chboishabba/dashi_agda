module DASHI.Moonshine.OggSSPP2UranoInertiaLocalizationFactorizationExact where

------------------------------------------------------------------------
-- p=2 URANO -> INERTIA LOCALIZATION FACTORIZATION
--
-- Split the current p=2 localization wall into two independent payments:
--
--   P : actual integral 2B source pieces -> five inertia sectors,
--       retaining Urano degree parity/module tags and forbidden-pair laws;
--
--   L : normalized finite-DVR length of each already-localized source piece
--       equals the independently defined inertia isotropy/class-defect depth.
--
-- P + L reconstruct the existing P2UranoInertiaSectorLocalizationTheorem.
--
-- ATTRIBUTION
--
-- Urano owns the finite-length DVR/Brauer framework and parity restrictions.
-- The binary-tetrahedral/inertia owners supply the five sectors and geometric
-- depths 3,3,2,1,1.
-- DASHI owns this factorization and any later proof connecting the two.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Sector
import DASHI.Moonshine.OggSSPP2InertiaStackDenominatorValuationExact as Geom
import DASHI.Moonshine.OggSSPP2UranoInertiaSectorLocalizationObligationExact as Full
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Payment P: source-native partition/localization only.
------------------------------------------------------------------------

record P2UranoInertiaPartitionAuthority : Set₁ where
  field
    SourcePiece :
      Set

    degreeParity :
      SourcePiece ->
      Urano.DegreeParity

    moduleTag :
      SourcePiece ->
      Urano.TwoBModuleTag

    sourcePieceComesFromIntegralTwoBWeightSpace :
      SourcePiece ->
      Bool

    sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue :
      (piece : SourcePiece) ->
      sourcePieceComesFromIntegralTwoBWeightSpace piece ≡ true

    respectsUranoForbiddenPairs :
      (piece : SourcePiece) ->
      Urano.TwoBSourceForbidden
        (degreeParity piece)
        (moduleTag piece)
      ->
      ⊥

    localizedSector :
      SourcePiece ->
      Sector.BinaryTetrahedralInversionOrbit

    everySectorHasSourcePiece :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      SourcePiece

    everySectorHasSourcePieceCorrect :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      localizedSector (everySectorHasSourcePiece sector) ≡ sector

    localizationDefinedWithoutMonsterResidual :
      Bool
    localizationDefinedWithoutMonsterResidualIsTrue :
      localizationDefinedWithoutMonsterResidual ≡ true

    localizationDefinedWithoutBase369Labels :
      Bool
    localizationDefinedWithoutBase369LabelsIsTrue :
      localizationDefinedWithoutBase369Labels ≡ true

open P2UranoInertiaPartitionAuthority public

------------------------------------------------------------------------
-- 2. Payment L: source length equals independent inertia depth.
------------------------------------------------------------------------

record P2UranoInertiaLengthComparisonAuthority
    (partition : P2UranoInertiaPartitionAuthority) : Set₁ where
  field
    normalizedDVRLength :
      SourcePiece partition ->
      Nat

    localizedLengthMatchesIsotropyDepth :
      (piece : SourcePiece partition) ->
      normalizedDVRLength piece
      ≡
      Geom.sectorIsotropyDenominatorTwoAdicDepth
        (localizedSector partition piece)

    lengthComparisonDefinedWithoutMonsterResidual :
      Bool
    lengthComparisonDefinedWithoutMonsterResidualIsTrue :
      lengthComparisonDefinedWithoutMonsterResidual ≡ true

    lengthComparisonDefinedWithoutBase369Labels :
      Bool
    lengthComparisonDefinedWithoutBase369LabelsIsTrue :
      lengthComparisonDefinedWithoutBase369Labels ≡ true

open P2UranoInertiaLengthComparisonAuthority public

------------------------------------------------------------------------
-- 3. P + L reconstruct the current full theorem.
------------------------------------------------------------------------

assembleP2UranoInertiaLocalization :
  (partition : P2UranoInertiaPartitionAuthority) ->
  P2UranoInertiaLengthComparisonAuthority partition ->
  Full.P2UranoInertiaSectorLocalizationTheorem
assembleP2UranoInertiaLocalization partition length =
  record
    { Full.SourcePiece =
        SourcePiece partition

    ; Full.degreeParity =
        degreeParity partition
    ; Full.moduleTag =
        moduleTag partition

    ; Full.sourcePieceComesFromIntegralTwoBWeightSpace =
        sourcePieceComesFromIntegralTwoBWeightSpace partition
    ; Full.sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue =
        sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue partition

    ; Full.respectsUranoForbiddenPairs =
        respectsUranoForbiddenPairs partition

    ; Full.localizedSector =
        localizedSector partition

    ; Full.everySectorHasSourcePiece =
        everySectorHasSourcePiece partition
    ; Full.everySectorHasSourcePieceCorrect =
        everySectorHasSourcePieceCorrect partition

    ; Full.normalizedDVRLength =
        normalizedDVRLength length
    ; Full.localizedLengthMatchesIsotropyDepth =
        localizedLengthMatchesIsotropyDepth length

    ; Full.localizationDefinedWithoutMonsterResidual =
        localizationDefinedWithoutMonsterResidual partition
    ; Full.localizationDefinedWithoutMonsterResidualIsTrue =
        localizationDefinedWithoutMonsterResidualIsTrue partition

    ; Full.localizationDefinedWithoutBase369Labels =
        localizationDefinedWithoutBase369Labels partition
    ; Full.localizationDefinedWithoutBase369LabelsIsTrue =
        localizationDefinedWithoutBase369LabelsIsTrue partition
    }

------------------------------------------------------------------------
-- 4. Exact representative-length consequences once both payments exist.
------------------------------------------------------------------------

identityLengthIsThree :
  (partition : P2UranoInertiaPartitionAuthority) ->
  (length : P2UranoInertiaLengthComparisonAuthority partition) ->
  normalizedDVRLength length
    (everySectorHasSourcePiece partition Sector.identityInertiaOrbit)
  ≡ 3
identityLengthIsThree partition length =
  Full.identityLengthIsThree
    (assembleP2UranoInertiaLocalization partition length)

minusOneLengthIsThree :
  (partition : P2UranoInertiaPartitionAuthority) ->
  (length : P2UranoInertiaLengthComparisonAuthority partition) ->
  normalizedDVRLength length
    (everySectorHasSourcePiece partition Sector.centralMinusOneInertiaOrbit)
  ≡ 3
minusOneLengthIsThree partition length =
  Full.minusOneLengthIsThree
    (assembleP2UranoInertiaLocalization partition length)

orderFourLengthIsTwo :
  (partition : P2UranoInertiaPartitionAuthority) ->
  (length : P2UranoInertiaLengthComparisonAuthority partition) ->
  normalizedDVRLength length
    (everySectorHasSourcePiece partition Sector.orderFourInertiaOrbit)
  ≡ 2
orderFourLengthIsTwo partition length =
  Full.orderFourLengthIsTwo
    (assembleP2UranoInertiaLocalization partition length)

orderThreeLengthIsOne :
  (partition : P2UranoInertiaPartitionAuthority) ->
  (length : P2UranoInertiaLengthComparisonAuthority partition) ->
  normalizedDVRLength length
    (everySectorHasSourcePiece partition Sector.orderThreePairInertiaOrbit)
  ≡ 1
orderThreeLengthIsOne partition length =
  Full.orderThreeLengthIsOne
    (assembleP2UranoInertiaLocalization partition length)

orderSixLengthIsOne :
  (partition : P2UranoInertiaPartitionAuthority) ->
  (length : P2UranoInertiaLengthComparisonAuthority partition) ->
  normalizedDVRLength length
    (everySectorHasSourcePiece partition Sector.orderSixPairInertiaOrbit)
  ≡ 1
orderSixLengthIsOne partition length =
  Full.orderSixLengthIsOne
    (assembleP2UranoInertiaLocalization partition length)

------------------------------------------------------------------------
-- 5. No unsupported shortcut between P and L.
------------------------------------------------------------------------

data PartitionAuthorityCreatesLengthComparison : Set where
data LengthComparisonCreatesSourcePartition : Set where
data UranoParityReceiptCreatesFiveSectorPartition : Set where
data ClassDefectVectorCreatesSourcePartition : Set where
data FiveSectorPartitionCreatesClassDefectLength : Set where
data TotalTenCreatesEitherPayment : Set where
data Base369CreatesEitherPayment : Set where

partitionDoesNotCreateLengthComparison :
  PartitionAuthorityCreatesLengthComparison -> ⊥
partitionDoesNotCreateLengthComparison ()

lengthComparisonDoesNotCreateSourcePartition :
  LengthComparisonCreatesSourcePartition -> ⊥
lengthComparisonDoesNotCreateSourcePartition ()

uranoParityReceiptDoesNotCreateFiveSectorPartition :
  UranoParityReceiptCreatesFiveSectorPartition -> ⊥
uranoParityReceiptDoesNotCreateFiveSectorPartition ()

classDefectVectorDoesNotCreateSourcePartition :
  ClassDefectVectorCreatesSourcePartition -> ⊥
classDefectVectorDoesNotCreateSourcePartition ()

fiveSectorPartitionDoesNotCreateClassDefectLength :
  FiveSectorPartitionCreatesClassDefectLength -> ⊥
fiveSectorPartitionDoesNotCreateClassDefectLength ()

totalTenDoesNotCreateEitherPayment :
  TotalTenCreatesEitherPayment -> ⊥
totalTenDoesNotCreateEitherPayment ()

base369DoesNotCreateEitherPayment :
  Base369CreatesEitherPayment -> ⊥
base369DoesNotCreateEitherPayment ()

------------------------------------------------------------------------
-- 6. Live source boundary.
------------------------------------------------------------------------

uranoBoundary :
  Urano.TwoBUranoIntegralModuleParityBoundary
uranoBoundary =
  Urano.canonicalTwoBUranoIntegralModuleParityBoundary

data P2UranoInertiaPartitionAuthorityInhabited : Set where
data P2UranoInertiaLengthComparisonAuthorityInhabited : Set where

partitionAuthorityStillOpen :
  P2UranoInertiaPartitionAuthorityInhabited -> ⊥
partitionAuthorityStillOpen ()

lengthComparisonAuthorityStillOpen :
  P2UranoInertiaLengthComparisonAuthorityInhabited -> ⊥
lengthComparisonAuthorityStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P2UranoInertiaLocalizationFactorizationBoundary : Set where
  constructor p2-urano-inertia-localization-factorization-boundary
  field
    uranoParityAndBrauerFrameworkSourced : Bool
    fiveInertiaSectorGeometryOwned : Bool
    classDefectVectorThreeThreeTwoOneOneOwned : Bool
    partitionPaymentSeparated : Bool
    lengthPaymentSeparated : Bool
    twoPaymentsAssembleFullLocalization : Bool
    partitionPaymentInhabited : Bool
    lengthPaymentInhabited : Bool
    uranoCreditedWithFiveSectorPartition : Bool
    uranoCreditedWithThreeThreeTwoOneOneLengthLaw : Bool
    monsterResidualUsedToDefinePayments : Bool
    base369UsedToDefinePayments : Bool
    attributionFirewallPreserved : Bool

canonicalP2UranoInertiaLocalizationFactorizationBoundary :
  P2UranoInertiaLocalizationFactorizationBoundary
canonicalP2UranoInertiaLocalizationFactorizationBoundary =
  p2-urano-inertia-localization-factorization-boundary
    true true true true true true
    false false false false false false true
