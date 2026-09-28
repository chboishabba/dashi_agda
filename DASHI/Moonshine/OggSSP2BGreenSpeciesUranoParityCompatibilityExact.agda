module DASHI.Moonshine.OggSSP2BGreenSpeciesUranoParityCompatibilityExact where

------------------------------------------------------------------------
-- 2B GREEN-SPECIES / URANO PARITY COMPATIBILITY
--
-- PURPOSE
--
-- Any future p=2 sectorwise Green/DVR localization must refine the actual
-- source-native integral Moonshine module rather than merely manufacture five
-- abstract classes with the desired lengths.
--
-- Urano's thesis supplies a necessary graded support condition for class 2B:
--
--   odd degree  : no trivial Z_2 summand;
--   even degree : no augmentation-quotient I_2 summand.
--
-- This module requires each proposed p=2 geometric sector class to reopen as a
-- finite direct sum of graded source pieces satisfying those exclusions.
--
-- It deliberately does NOT identify an Urano indecomposable tag with any
-- binary-tetrahedral inertia sector.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact as Green
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Fold source-native pieces in the proposed Green species.
------------------------------------------------------------------------

record TwoBSourcePiece
    (A : Green.PBGreenRingSectorSpeciesAuthority) : Set₁ where
  constructor two-b-source-piece
  field
    Piece : Set

    degreeParity :
      Piece ->
      Urano.DegreeParity

    moduleTag :
      Piece ->
      Urano.TwoBModuleTag

    moduleClass :
      Piece ->
      Green.ModuleClass (Green.species A)

    respectsUranoForbiddenPairs :
      (piece : Piece) ->
      Urano.TwoBSourceForbidden
        (degreeParity piece)
        (moduleTag piece)
      ->
      ⊥

open TwoBSourcePiece public

foldSourcePieces :
  {A : Green.PBGreenRingSectorSpeciesAuthority} ->
  (source : TwoBSourcePiece A) ->
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
-- 2. Every p=2 geometric sector class must reopen through source pieces.
------------------------------------------------------------------------

record TwoBGreenSpeciesUranoParityCompatibility
    (A : Green.PBGreenRingSectorSpeciesAuthority) : Set₁ where
  field
    sourcePieces :
      TwoBSourcePiece A

    sectorSourcePieces :
      Preferred.Sector Preferred.p2PreferredPresentation ->
      List (Piece sourcePieces)

    sectorClassReopensFromSourcePieces :
      (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
      Green.p2SectorClass A sector
      ≡
      foldSourcePieces
        sourcePieces
        (sectorSourcePieces sector)

    sourcePiecesComeFromTwoBWeightSpaces :
      Bool
    sourcePiecesComeFromTwoBWeightSpacesIsTrue :
      sourcePiecesComeFromTwoBWeightSpaces ≡ true

    gradedFunctionalAgreesWithUranoTwoBHauptmodulReceipt :
      Bool
    gradedFunctionalAgreesWithUranoTwoBHauptmodulReceiptIsTrue :
      gradedFunctionalAgreesWithUranoTwoBHauptmodulReceipt ≡ true

    refinementDoesNotIdentifyModuleTagsWithInertiaLabels :
      Bool
    refinementDoesNotIdentifyModuleTagsWithInertiaLabelsIsTrue :
      refinementDoesNotIdentifyModuleTagsWithInertiaLabels ≡ true

open TwoBGreenSpeciesUranoParityCompatibility public

------------------------------------------------------------------------
-- 3. Necessary consequence: every source piece is non-forbidden.
------------------------------------------------------------------------

sourcePieceCannotRealizeForbiddenUranoPair :
  {A : Green.PBGreenRingSectorSpeciesAuthority} ->
  (compatibility : TwoBGreenSpeciesUranoParityCompatibility A) ->
  (piece : Piece (sourcePieces compatibility)) ->
  Urano.TwoBSourceForbidden
    (degreeParity (sourcePieces compatibility) piece)
    (moduleTag (sourcePieces compatibility) piece)
  ->
  ⊥
sourcePieceCannotRealizeForbiddenUranoPair compatibility piece forbidden =
  respectsUranoForbiddenPairs
    (sourcePieces compatibility)
    piece
    forbidden

------------------------------------------------------------------------
-- 4. Attribution / non-promotion boundary.
------------------------------------------------------------------------

data UranoParityDeterminesInertiaSector : Set where
data T4AHauptmodulDeterminesSectorLengths : Set where
data FiveSectorClassDeterminesIndecomposableDecomposition : Set where
data ParityCompatibilityInhabitsGreenSpecies : Set where

uranoParityDoesNotDetermineInertiaSector :
  UranoParityDeterminesInertiaSector -> ⊥
uranoParityDoesNotDetermineInertiaSector ()

t4ADoesNotDetermineSectorLengths :
  T4AHauptmodulDeterminesSectorLengths -> ⊥
t4ADoesNotDetermineSectorLengths ()

sectorClassDoesNotDetermineIndecomposableDecomposition :
  FiveSectorClassDeterminesIndecomposableDecomposition -> ⊥
sectorClassDoesNotDetermineIndecomposableDecomposition ()

parityCompatibilityDoesNotInhabitGreenSpecies :
  ParityCompatibilityInhabitsGreenSpecies -> ⊥
parityCompatibilityDoesNotInhabitGreenSpecies ()

------------------------------------------------------------------------
-- 5. Live theorem wall.
------------------------------------------------------------------------

data TwoBGreenSpeciesUranoParityCompatibilityInhabited : Set where

twoBGreenSpeciesUranoParityCompatibilityStillOpen :
  TwoBGreenSpeciesUranoParityCompatibilityInhabited -> ⊥
twoBGreenSpeciesUranoParityCompatibilityStillOpen ()

uranoParityBoundary :
  Urano.TwoBUranoIntegralModuleParityBoundary
uranoParityBoundary =
  Urano.canonicalTwoBUranoIntegralModuleParityBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record TwoBGreenSpeciesUranoParityCompatibilityBoundary : Set where
  constructor two-b-green-species-urano-parity-compatibility-boundary
  field
    uranoParityExclusionsSourced : Bool
    uranoTwoBHauptmodulFunctionalSourced : Bool
    sourcePieceRefinementInterfaceSpecified : Bool
    everySourcePieceMustRespectParityExclusions : Bool
    everyP2SectorMustReopenThroughSourcePieces : Bool
    moduleTagsIdentifiedWithInertiaLabels : Bool
    parityCompatibilityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalTwoBGreenSpeciesUranoParityCompatibilityBoundary :
  TwoBGreenSpeciesUranoParityCompatibilityBoundary
canonicalTwoBGreenSpeciesUranoParityCompatibilityBoundary =
  two-b-green-species-urano-parity-compatibility-boundary
    true true true true true false false true
