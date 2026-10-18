module DASHI.Moonshine.OggSSP3BGreenSpeciesCarnahanFixedVectorCompatibilityExact where

------------------------------------------------------------------------
-- 3B GREEN-SPECIES / CARNAHAN H_3 FIXED-VECTOR COMPATIBILITY
--
-- PURPOSE
--
-- A future p=3 node/branch localization must be a refinement of the actual
-- source-native integral Moonshine module, not an abstract two-piece carrier
-- manufactured from the desired geometric multiplicities.
--
-- Carnahan supplies an order-9 3B-pure H_3 decomposition into pieces that,
-- after the stated base extension, embed equivariantly into the 3B-fixed
-- vectors.  This module requires every proposed p=3 geometric sector class to
-- reopen through such source-native pieces.
--
-- No source piece is identified with the node or branch-pair sector.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact as Green
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSP3BCarnahanOrderNineFixedVectorRefinementExact as Carnahan
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-native H_3 pieces carried into the proposed Green species.
------------------------------------------------------------------------

record ThreeBSourcePiece
    (A : Green.PBGreenRingSectorSpeciesAuthority) : Set₁ where
  constructor three-b-source-piece
  field
    Piece : Set

    moduleClass :
      Piece ->
      Green.ModuleClass (Green.species A)

    comesFromCarnahanH3Decomposition :
      (piece : Piece) ->
      Bool

    comesFromCarnahanH3DecompositionIsTrue :
      (piece : Piece) ->
      comesFromCarnahanH3Decomposition piece ≡ true

    embedsEquivariantlyIntoThreeBFixedVectors :
      (piece : Piece) ->
      Bool

    embedsEquivariantlyIntoThreeBFixedVectorsIsTrue :
      (piece : Piece) ->
      embedsEquivariantlyIntoThreeBFixedVectors piece ≡ true

open ThreeBSourcePiece public

foldSourcePieces :
  {A : Green.PBGreenRingSectorSpeciesAuthority} ->
  (source : ThreeBSourcePiece A) ->
  List (Piece source) ->
  Green.ModuleClass (Green.species A)
foldSourcePieces {A} source [] =
  Green.zeroClass (Green.species A)
foldSourcePieces {A} source (piece ∷ rest) =
  Green.directSum
    (Green.species A)
    (moduleClass source piece)
    (foldSourcePieces source rest)

------------------------------------------------------------------------
-- 1b. Additive normalized length of a source-piece fold.
------------------------------------------------------------------------

sourcePieceLength :
  {A : Green.PBGreenRingSectorSpeciesAuthority} ->
  (source : ThreeBSourcePiece A) ->
  Piece source ->
  Nat
sourcePieceLength {A} source piece =
  Green.normalizedDVRLength A (moduleClass source piece)

sumSourcePieceLengths :
  {A : Green.PBGreenRingSectorSpeciesAuthority} ->
  (source : ThreeBSourcePiece A) ->
  List (Piece source) ->
  Nat
sumSourcePieceLengths source [] = 0
sumSourcePieceLengths source (piece ∷ rest) =
  sourcePieceLength source piece
  + sumSourcePieceLengths source rest

foldSourcePiecesLengthIsSum :
  {A : Green.PBGreenRingSectorSpeciesAuthority} ->
  (source : ThreeBSourcePiece A) ->
  (pieces : List (Piece source)) ->
  Green.normalizedDVRLength A
    (foldSourcePieces source pieces)
  ≡
  sumSourcePieceLengths source pieces
foldSourcePiecesLengthIsSum {A} source [] =
  trans
    (sym
      (Green.speciesValueIsNormalizedDVRLength A
        (Green.zeroClass (Green.species A))))
    (Green.speciesZero (Green.species A))
foldSourcePiecesLengthIsSum {A} source (piece ∷ rest) =
  trans
    (Green.normalizedLengthDirectSum A
      (moduleClass source piece)
      (foldSourcePieces source rest))
    (cong₂ _+_
      refl
      (foldSourcePiecesLengthIsSum source rest))

------------------------------------------------------------------------
-- 2. Every geometric p=3 sector class must reopen through H_3 pieces.
------------------------------------------------------------------------

record ThreeBGreenSpeciesCarnahanCompatibility
    (A : Green.PBGreenRingSectorSpeciesAuthority) : Set₁ where
  field
    sourcePieces :
      ThreeBSourcePiece A

    sectorSourcePieces :
      Preferred.Sector Preferred.p3PreferredPresentation ->
      List (Piece sourcePieces)

    sectorClassReopensFromSourcePieces :
      (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
      Green.p3SectorClass A sector
      ≡
      foldSourcePieces
        sourcePieces
        (sectorSourcePieces sector)

    refinementUsesCarnahanBaseExtendedSetting :
      Bool
    refinementUsesCarnahanBaseExtendedSettingIsTrue :
      refinementUsesCarnahanBaseExtendedSetting ≡ true

    refinementPreservesRelevantCentralizerNormalizerEquivariance :
      Bool
    refinementPreservesRelevantCentralizerNormalizerEquivarianceIsTrue :
      refinementPreservesRelevantCentralizerNormalizerEquivariance ≡ true

    refinementDoesNotIdentifyH3PiecesWithNodeBranchLabels :
      Bool
    refinementDoesNotIdentifyH3PiecesWithNodeBranchLabelsIsTrue :
      refinementDoesNotIdentifyH3PiecesWithNodeBranchLabels ≡ true

open ThreeBGreenSpeciesCarnahanCompatibility public

sectorLengthIsSumOfCarnahanSourcePieceLengths :
  {A : Green.PBGreenRingSectorSpeciesAuthority} ->
  (compatibility : ThreeBGreenSpeciesCarnahanCompatibility A) ->
  (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
  Green.normalizedDVRLength A
    (Green.p3SectorClass A sector)
  ≡
  sumSourcePieceLengths
    (sourcePieces compatibility)
    (sectorSourcePieces compatibility sector)
sectorLengthIsSumOfCarnahanSourcePieceLengths {A} compatibility sector =
  trans
    (cong
      (Green.normalizedDVRLength A)
      (sectorClassReopensFromSourcePieces compatibility sector))
    (foldSourcePiecesLengthIsSum
      (sourcePieces compatibility)
      (sectorSourcePieces compatibility sector))

------------------------------------------------------------------------
-- 3. Sourced provenance consequence.
------------------------------------------------------------------------

everySourcePieceHasFixedVectorEmbedding :
  {A : Green.PBGreenRingSectorSpeciesAuthority} ->
  (compatibility : ThreeBGreenSpeciesCarnahanCompatibility A) ->
  (piece : Piece (sourcePieces compatibility)) ->
  embedsEquivariantlyIntoThreeBFixedVectors
    (sourcePieces compatibility)
    piece
  ≡ true
everySourcePieceHasFixedVectorEmbedding compatibility piece =
  embedsEquivariantlyIntoThreeBFixedVectorsIsTrue
    (sourcePieces compatibility)
    piece

------------------------------------------------------------------------
-- 4. Attribution firewalls.
------------------------------------------------------------------------

data CarnahanH3PieceIsNodeSector : Set where
data CarnahanH3PieceIsBranchSector : Set where
data H3DecompositionDeterminesTwoSectorPartition : Set where
data FixedVectorEmbeddingDeterminesUranoLengthOne : Set where
data H3CompatibilityInhabitsGreenSpecies : Set where

h3PieceNotIdentifiedWithNodeSector :
  CarnahanH3PieceIsNodeSector -> ⊥
h3PieceNotIdentifiedWithNodeSector ()

h3PieceNotIdentifiedWithBranchSector :
  CarnahanH3PieceIsBranchSector -> ⊥
h3PieceNotIdentifiedWithBranchSector ()

h3DecompositionDoesNotDetermineTwoSectorPartition :
  H3DecompositionDeterminesTwoSectorPartition -> ⊥
h3DecompositionDoesNotDetermineTwoSectorPartition ()

fixedVectorEmbeddingDoesNotDetermineUranoLengthOne :
  FixedVectorEmbeddingDeterminesUranoLengthOne -> ⊥
fixedVectorEmbeddingDoesNotDetermineUranoLengthOne ()

h3CompatibilityDoesNotInhabitGreenSpecies :
  H3CompatibilityInhabitsGreenSpecies -> ⊥
h3CompatibilityDoesNotInhabitGreenSpecies ()

------------------------------------------------------------------------
-- 5. Live boundary.
------------------------------------------------------------------------

carnahanBoundary :
  Carnahan.ThreeBCarnahanOrderNineRefinementBoundary
carnahanBoundary =
  Carnahan.canonicalThreeBCarnahanOrderNineRefinementBoundary

data ThreeBGreenSpeciesCarnahanCompatibilityInhabited : Set where

threeBGreenSpeciesCarnahanCompatibilityStillOpen :
  ThreeBGreenSpeciesCarnahanCompatibilityInhabited -> ⊥
threeBGreenSpeciesCarnahanCompatibilityStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record ThreeBGreenSpeciesCarnahanCompatibilityBoundary : Set where
  constructor three-b-green-species-carnahan-compatibility-boundary
  field
    orderNineThreeBRefinementSourced : Bool
    fixedVectorEmbeddingSourced : Bool
    sourcePieceRefinementInterfaceSpecified : Bool
    everyP3SectorMustReopenThroughSourcePieces : Bool
    baseExtensionQualificationRetained : Bool
    sourcePiecesIdentifiedWithNodeBranchLabels : Bool
    compatibilityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalThreeBGreenSpeciesCarnahanCompatibilityBoundary :
  ThreeBGreenSpeciesCarnahanCompatibilityBoundary
canonicalThreeBGreenSpeciesCarnahanCompatibilityBoundary =
  three-b-green-species-carnahan-compatibility-boundary
    true true true true true false false true
