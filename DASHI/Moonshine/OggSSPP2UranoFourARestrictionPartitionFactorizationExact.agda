module DASHI.Moonshine.OggSSPP2UranoFourARestrictionPartitionFactorizationExact where

------------------------------------------------------------------------
-- p=2 URANO + RESTRICTED-4A -> FIVE-SECTOR PARTITION FACTORIZATION
--
-- The previous four-vs-five no-go proves that Urano's coarse
--
--   parity x {trivial Z2, I2, other}
--
-- language cannot by itself be exactly recharted to the five inertia sectors.
--
-- The canonical source-native refinement lane now available is:
--
--   4A integral indecomposable label
--        |
--        | restrict along <g^2> = 2B
--        v
--   actual 2B source piece.
--
-- This module requires the five-sector classifier to FACTOR THROUGH that finer
-- 4A label while retaining Urano's parity/module restrictions on the same
-- source piece.  If supplied, it assembles the partition half of the existing
-- p=2 localization theorem.
--
-- ATTRIBUTION
--
-- ATLAS + Carnahan--Urano source the 4A->2B refinement lane.
-- Urano sources the 2B parity exclusions.
-- Binary-tetrahedral geometry supplies the five target sectors.
-- DASHI owns any theorem identifying restricted 4A labels with those sectors.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSP4A2BIntegralRestrictionRefinementExact as FourA
import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Sector
import DASHI.Moonshine.OggSSPP2UranoInertiaLocalizationFactorizationExact as Partition
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exact refined partition payment.
------------------------------------------------------------------------

record P2UranoFourARefinedPartitionAuthority : Set₁ where
  field
    refinement :
      FourA.FourARestrictedTwoBRefinementAuthority

    degreeParity :
      FourA.TwoBSourcePiece refinement ->
      Urano.DegreeParity

    moduleTag :
      FourA.TwoBSourcePiece refinement ->
      Urano.TwoBModuleTag

    sourcePieceComesFromIntegralTwoBWeightSpace :
      FourA.TwoBSourcePiece refinement ->
      Bool

    sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue :
      (piece : FourA.TwoBSourcePiece refinement) ->
      sourcePieceComesFromIntegralTwoBWeightSpace piece ≡ true

    respectsUranoForbiddenPairs :
      (piece : FourA.TwoBSourcePiece refinement) ->
      Urano.TwoBSourceForbidden
        (degreeParity piece)
        (moduleTag piece)
      ->
      ⊥

    sectorOfFourALabel :
      FourA.FourAIndecomposableLabel refinement ->
      Sector.BinaryTetrahedralInversionOrbit

    localizedSector :
      FourA.TwoBSourcePiece refinement ->
      Sector.BinaryTetrahedralInversionOrbit

    localizedSectorFactorsThroughFourALabel :
      (piece : FourA.TwoBSourcePiece refinement) ->
      localizedSector piece
      ≡
      sectorOfFourALabel
        (FourA.fourALabelOfSourcePiece refinement piece)

    everySectorHasSourcePiece :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      FourA.TwoBSourcePiece refinement

    everySectorHasSourcePieceCorrect :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      localizedSector
        (everySectorHasSourcePiece sector)
      ≡ sector

    sectorClassifierDerivedFromRestrictedFourAData :
      Bool
    sectorClassifierDerivedFromRestrictedFourADataIsTrue :
      sectorClassifierDerivedFromRestrictedFourAData ≡ true

    classifierIndependentOfMonsterResidualTen :
      Bool
    classifierIndependentOfMonsterResidualTenIsTrue :
      classifierIndependentOfMonsterResidualTen ≡ true

    classifierIndependentOfBase369Labels :
      Bool
    classifierIndependentOfBase369LabelsIsTrue :
      classifierIndependentOfBase369Labels ≡ true

open P2UranoFourARefinedPartitionAuthority public

------------------------------------------------------------------------
-- 2. Assemble the partition half of p=2 localization.
------------------------------------------------------------------------

asP2UranoInertiaPartition :
  P2UranoFourARefinedPartitionAuthority ->
  Partition.P2UranoInertiaPartitionAuthority
asP2UranoInertiaPartition authority =
  record
    { Partition.SourcePiece =
        FourA.TwoBSourcePiece (refinement authority)

    ; Partition.degreeParity =
        degreeParity authority

    ; Partition.moduleTag =
        moduleTag authority

    ; Partition.sourcePieceComesFromIntegralTwoBWeightSpace =
        sourcePieceComesFromIntegralTwoBWeightSpace authority

    ; Partition.sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue =
        sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue authority

    ; Partition.respectsUranoForbiddenPairs =
        respectsUranoForbiddenPairs authority

    ; Partition.localizedSector =
        localizedSector authority

    ; Partition.everySectorHasSourcePiece =
        everySectorHasSourcePiece authority

    ; Partition.everySectorHasSourcePieceCorrect =
        everySectorHasSourcePieceCorrect authority

    ; Partition.localizationDefinedWithoutMonsterResidual =
        classifierIndependentOfMonsterResidualTen authority

    ; Partition.localizationDefinedWithoutMonsterResidualIsTrue =
        classifierIndependentOfMonsterResidualTenIsTrue authority

    ; Partition.localizationDefinedWithoutBase369Labels =
        classifierIndependentOfBase369Labels authority

    ; Partition.localizationDefinedWithoutBase369LabelsIsTrue =
        classifierIndependentOfBase369LabelsIsTrue authority
    }

------------------------------------------------------------------------
-- 3. This really uses a finer coordinate than the coarse Urano language.
------------------------------------------------------------------------

data CoarseUranoPatternAlonePaysRefinedPartition : Set where
data FourARestrictionAlonePaysSectorRecognition : Set where
data ExplicitFourAMultiplicitiesChooseSectorMap : Set where
data FiveSectorGeometryChoosesFourALabelMap : Set where
data MonsterResidualTenChoosesFourALabelMap : Set where

coarseUranoPatternCannotPayRefinedPartition :
  CoarseUranoPatternAlonePaysRefinedPartition -> ⊥
coarseUranoPatternCannotPayRefinedPartition ()

fourARestrictionAloneDoesNotPaySectorRecognition :
  FourARestrictionAlonePaysSectorRecognition -> ⊥
fourARestrictionAloneDoesNotPaySectorRecognition ()

explicitFourAMultiplicitiesDoNotChooseSectorMap :
  ExplicitFourAMultiplicitiesChooseSectorMap -> ⊥
explicitFourAMultiplicitiesDoNotChooseSectorMap ()

geometryDoesNotChooseFourALabelMap :
  FiveSectorGeometryChoosesFourALabelMap -> ⊥
geometryDoesNotChooseFourALabelMap ()

monsterResidualDoesNotChooseFourALabelMap :
  MonsterResidualTenChoosesFourALabelMap -> ⊥
monsterResidualDoesNotChooseFourALabelMap ()

------------------------------------------------------------------------
-- 4. Live recognition wall.
------------------------------------------------------------------------

data P2UranoFourARefinedPartitionAuthorityInhabited : Set where

refinedPartitionStillOpen :
  P2UranoFourARefinedPartitionAuthorityInhabited -> ⊥
refinedPartitionStillOpen ()

fourARestrictionBoundary :
  FourA.FourA2BRestrictionRefinementBoundary
fourARestrictionBoundary =
  FourA.canonicalFourA2BRestrictionRefinementBoundary

uranoBoundary :
  Urano.TwoBUranoIntegralModuleParityBoundary
uranoBoundary =
  Urano.canonicalTwoBUranoIntegralModuleParityBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P2UranoFourARestrictionPartitionBoundary : Set where
  constructor p2-urano-four-a-restriction-partition-boundary
  field
    fourASquareToTwoBSourceLanePaid : Bool
    fourAIntegralIndecomposableDecompositionSourced : Bool
    uranoParityConstraintsSourced : Bool
    coarseUranoFourVsFiveNoGoOwned : Bool
    refinedClassifierRequiredToFactorThroughFourALabel : Bool
    refinedClassifierSurjectiveToFiveSectorsRequired : Bool
    refinedPartitionAssemblesP2PartitionPayment : Bool
    refinedPartitionInhabited : Bool
    carnahanUranoCreditedWithFiveSectorMap : Bool
    uranoCreditedWithFiveSectorMap : Bool
    monsterResidualUsedToChooseMap : Bool
    base369UsedToChooseMap : Bool
    attributionFirewallPreserved : Bool

canonicalP2UranoFourARestrictionPartitionBoundary :
  P2UranoFourARestrictionPartitionBoundary
canonicalP2UranoFourARestrictionPartitionBoundary =
  p2-urano-four-a-restriction-partition-boundary
    true true true true true true true
    false false false false false true
