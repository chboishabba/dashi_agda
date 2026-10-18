module DASHI.Moonshine.OggSSPP2GreenClassSectorRecognitionExact where

------------------------------------------------------------------------
-- p=2 SOURCE GREEN-CLASS -> FIVE INERTIA-SECTOR RECOGNITION
--
-- LIVE CONCLUSION FROM THE FINITE NO-GO CHAIN
--
-- None of the following source-native cyclic coordinates is large enough to
-- classify the five p=2 inertia sectors:
--
--   * Urano parity/module-tag language:                     <= 4 patterns;
--   * actual restricted 4A indecomposable type:             3 labels;
--   * restricted 4A type + degree parity:                   4 patterns;
--   * restricted 4A type + parity + 2B Tate support:        4 patterns.
--
-- Therefore the next admissible classifier must retain information that is
-- invisible to the underlying cyclic lattice type.  The existing terminal
-- architecture already names exactly such an object: the source-side
-- Green/Brauer module class with Monster-local centralizer action retained.
--
-- THIS MODULE DOES NOT INVENT FIVE GREEN CLASSES.
--
-- It specifies the exact recognition theorem a real source construction must
-- pay: sector identity must FACTOR THROUGH the source Green class, and every
-- geometric sector must be witnessed by an actual non-forbidden 2B source
-- piece carrying such a class.
--
-- Attribution:
--   Carnahan--Urano / Urano own the Green-ring and generalized-Brauer
--   frameworks.
--   The binary-tetrahedral geometry owns the five sectors.
--   DASHI owns only this recognition/factorization obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Sector
import DASHI.Moonshine.OggSSPP2UranoInertiaLocalizationFactorizationExact as Partition
import DASHI.Moonshine.OggSSPP2UranoParityFiveSectorNoGoExact as ParityNoGo
import DASHI.Moonshine.OggSSP4A2BThreeLabelFiveSectorNoGoExact as FourANoGo
import DASHI.Moonshine.OggSSP4A2BTateRefinementFiveSectorNoGoExact as TateNoGo
import DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact as Green
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Minimal source-side Green-class refinement.
--
-- This deliberately stops short of PBGreenRingSectorSpeciesAuthority, because
-- that larger record already contains the sector classes and geometric length
-- payment we are trying to construct.  Here GreenClass is SOURCE data only.
------------------------------------------------------------------------

record P2SourceGreenClassRefinement : Set₁ where
  field
    SourcePiece :
      Set

    GreenClass :
      Set

    degreeParity :
      SourcePiece ->
      Urano.DegreeParity

    moduleTag :
      SourcePiece ->
      Urano.TwoBModuleTag

    greenClass :
      SourcePiece ->
      GreenClass

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

    greenClassComesFromRelevantIntegralGreenRing :
      SourcePiece ->
      Bool

    greenClassComesFromRelevantIntegralGreenRingIsTrue :
      (piece : SourcePiece) ->
      greenClassComesFromRelevantIntegralGreenRing piece ≡ true

    greenClassRetainsMonsterLocalCentralizerAction :
      SourcePiece ->
      Bool

    greenClassRetainsMonsterLocalCentralizerActionIsTrue :
      (piece : SourcePiece) ->
      greenClassRetainsMonsterLocalCentralizerAction piece ≡ true

    greenClassSupportsGeneralizedBrauerCharacter :
      SourcePiece ->
      Bool

    greenClassSupportsGeneralizedBrauerCharacterIsTrue :
      (piece : SourcePiece) ->
      greenClassSupportsGeneralizedBrauerCharacter piece ≡ true

    refinementDefinedWithoutMonsterResidualTen :
      Bool
    refinementDefinedWithoutMonsterResidualTenIsTrue :
      refinementDefinedWithoutMonsterResidualTen ≡ true

    refinementDefinedWithoutBase369Labels :
      Bool
    refinementDefinedWithoutBase369LabelsIsTrue :
      refinementDefinedWithoutBase369Labels ≡ true

open P2SourceGreenClassRefinement public

------------------------------------------------------------------------
-- 2. Recognition payment: sector is a consumer of GreenClass.
------------------------------------------------------------------------

record P2GreenClassSectorRecognition
    (source : P2SourceGreenClassRefinement) : Set₁ where
  field
    sectorOfGreenClass :
      GreenClass source ->
      Sector.BinaryTetrahedralInversionOrbit

    localizedSector :
      SourcePiece source ->
      Sector.BinaryTetrahedralInversionOrbit

    localizedSectorFactorsThroughGreenClass :
      (piece : SourcePiece source) ->
      localizedSector piece
      ≡
      sectorOfGreenClass (greenClass source piece)

    everySectorHasSourcePiece :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      SourcePiece source

    everySectorHasSourcePieceCorrect :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      localizedSector (everySectorHasSourcePiece sector) ≡ sector

    recognitionIndependentOfMonsterResidualTen :
      Bool
    recognitionIndependentOfMonsterResidualTenIsTrue :
      recognitionIndependentOfMonsterResidualTen ≡ true

    recognitionIndependentOfBase369Labels :
      Bool
    recognitionIndependentOfBase369LabelsIsTrue :
      recognitionIndependentOfBase369Labels ≡ true

open P2GreenClassSectorRecognition public

------------------------------------------------------------------------
-- 3. A paid Green-class recognition gives the partition half of localization.
------------------------------------------------------------------------

asUranoInertiaPartition :
  (source : P2SourceGreenClassRefinement) ->
  P2GreenClassSectorRecognition source ->
  Partition.P2UranoInertiaPartitionAuthority
asUranoInertiaPartition source recognition =
  record
    { Partition.SourcePiece =
        SourcePiece source

    ; Partition.degreeParity =
        degreeParity source

    ; Partition.moduleTag =
        moduleTag source

    ; Partition.sourcePieceComesFromIntegralTwoBWeightSpace =
        sourcePieceComesFromIntegralTwoBWeightSpace source

    ; Partition.sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue =
        sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue source

    ; Partition.respectsUranoForbiddenPairs =
        respectsUranoForbiddenPairs source

    ; Partition.localizedSector =
        localizedSector recognition

    ; Partition.everySectorHasSourcePiece =
        everySectorHasSourcePiece recognition

    ; Partition.everySectorHasSourcePieceCorrect =
        everySectorHasSourcePieceCorrect recognition

    ; Partition.localizationDefinedWithoutMonsterResidual =
        recognitionIndependentOfMonsterResidualTen recognition

    ; Partition.localizationDefinedWithoutMonsterResidualIsTrue =
        recognitionIndependentOfMonsterResidualTenIsTrue recognition

    ; Partition.localizationDefinedWithoutBase369Labels =
        recognitionIndependentOfBase369Labels recognition

    ; Partition.localizationDefinedWithoutBase369LabelsIsTrue =
        recognitionIndependentOfBase369LabelsIsTrue recognition
    }

------------------------------------------------------------------------
-- 4. The recognition must genuinely refine the already-failed coordinates.
--
-- We do NOT postulate which collision is split.  We only make explicit that a
-- future source theorem must carry information beyond all three coarse lanes.
------------------------------------------------------------------------

data GreenClassMayFactorThroughUranoParityTag : Set where
data GreenClassMayFactorThroughRestrictedFourALabelParity : Set where
data GreenClassMayFactorThroughRestrictedFourATatePattern : Set where
data GeometryMayDefineGreenClass : Set where
data MonsterResidualMayDefineGreenClass : Set where

greenClassCannotBeReplacedByUranoParityTag :
  GreenClassMayFactorThroughUranoParityTag -> ⊥
greenClassCannotBeReplacedByUranoParityTag ()

greenClassCannotBeReplacedByFourALabelParity :
  GreenClassMayFactorThroughRestrictedFourALabelParity -> ⊥
greenClassCannotBeReplacedByFourALabelParity ()

greenClassCannotBeReplacedByFourATatePattern :
  GreenClassMayFactorThroughRestrictedFourATatePattern -> ⊥
greenClassCannotBeReplacedByFourATatePattern ()

geometryMayNotManufactureGreenClass :
  GeometryMayDefineGreenClass -> ⊥
geometryMayNotManufactureGreenClass ()

monsterResidualMayNotManufactureGreenClass :
  MonsterResidualMayDefineGreenClass -> ⊥
monsterResidualMayNotManufactureGreenClass ()

------------------------------------------------------------------------
-- 5. Existing no-go / framework receipts.
------------------------------------------------------------------------

uranoParityNoGoBoundary :
  ParityNoGo.P2UranoParityFiveSectorNoGoBoundary
uranoParityNoGoBoundary =
  ParityNoGo.canonicalP2UranoParityFiveSectorNoGoBoundary

fourALabelNoGoBoundary :
  FourANoGo.FourA2BThreeLabelFiveSectorNoGoBoundary
fourALabelNoGoBoundary =
  FourANoGo.canonicalFourA2BThreeLabelFiveSectorNoGoBoundary

fourATateNoGoBoundary :
  TateNoGo.FourA2BTateRefinementFiveSectorNoGoBoundary
fourATateNoGoBoundary =
  TateNoGo.canonicalFourA2BTateRefinementFiveSectorNoGoBoundary

greenSpeciesFrameworkBoundary :
  Green.PBGreenRingSectorSpeciesBoundary
greenSpeciesFrameworkBoundary =
  Green.canonicalPBGreenRingSectorSpeciesBoundary

------------------------------------------------------------------------
-- 6. Live wall.
------------------------------------------------------------------------

data P2SourceGreenClassRefinementInhabited : Set where
data P2GreenClassSectorRecognitionInhabited : Set where

sourceGreenClassRefinementStillOpen :
  P2SourceGreenClassRefinementInhabited -> ⊥
sourceGreenClassRefinementStillOpen ()

greenClassSectorRecognitionStillOpen :
  P2GreenClassSectorRecognitionInhabited -> ⊥
greenClassSectorRecognitionStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P2GreenClassSectorRecognitionBoundary : Set where
  constructor p2-green-class-sector-recognition-boundary
  field
    greenBrauerFrameworkSourced : Bool
    centralizerActionRetentionRequired : Bool
    generalizedBrauerCompatibilityRequired : Bool
    sourceGreenClassMustPreexistGeometry : Bool
    sectorClassifierFactorsThroughGreenClass : Bool
    everySectorNeedsActualSourceWitness : Bool
    partitionAdapterOwned : Bool
    uranoParityReplacementBlocked : Bool
    fourALabelParityReplacementBlocked : Bool
    fourATateReplacementBlocked : Bool
    sourceGreenClassRefinementInhabited : Bool
    greenClassSectorRecognitionInhabited : Bool
    monsterResidualUsedToDefineGreenClass : Bool
    base369UsedToDefineGreenClass : Bool
    attributionFirewallPreserved : Bool

canonicalP2GreenClassSectorRecognitionBoundary :
  P2GreenClassSectorRecognitionBoundary
canonicalP2GreenClassSectorRecognitionBoundary =
  p2-green-class-sector-recognition-boundary
    true true true true true true true
    true true true
    false false false false true
