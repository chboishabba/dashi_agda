module DASHI.Moonshine.OggSSPP3H3NodeBranchLocalizationObligationExact where

------------------------------------------------------------------------
-- p=3 H_3 -> DELIGNE--RAPOPORT NODE/BRANCH LOCALIZATION OBLIGATION
--
-- EXISTING SOURCE-BACKED INPUT
--
-- Carnahan supplies, after the stated base extension:
--   * a 3B-pure order-9 group H_3;
--   * a decomposition of the integral Moonshine form into pieces;
--   * equivariant embeddings of those pieces into 3B-fixed vectors.
--
-- EXISTING GEOMETRIC INPUT
--
-- Deligne--Rapoport supplies the two local orbit sectors:
--   * supersingular node;
--   * Frobenius/Verschiebung branch pair.
--
-- MISSING THEOREM
--
-- Refine Carnahan's source pieces by a target-independent prime-level
-- localization functor to those two geometric sectors, and prove normalized
-- finite-DVR length one on each sector.
--
-- This theorem may not be defined from:
--   * the Monster residual 2;
--   * the Duncan--Swisher exceptional gap;
--   * Base369 labels.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP3BCarnahanOrderNineFixedVectorRefinementExact as Carnahan
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as DR
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalMultiplicityExact as Geom
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Minimal theorem interface.
------------------------------------------------------------------------

record P3H3NodeBranchLocalizationTheorem : Set₁ where
  field
    H3Piece :
      Set

    pieceComesFromCarnahanOrderNineDecomposition :
      H3Piece ->
      Bool

    pieceComesFromCarnahanOrderNineDecompositionIsTrue :
      (piece : H3Piece) ->
      pieceComesFromCarnahanOrderNineDecomposition piece ≡ true

    pieceEmbedsEquivariantlyIntoThreeBFixedVectors :
      H3Piece ->
      Bool

    pieceEmbedsEquivariantlyIntoThreeBFixedVectorsIsTrue :
      (piece : H3Piece) ->
      pieceEmbedsEquivariantlyIntoThreeBFixedVectors piece ≡ true

    localizedSector :
      H3Piece ->
      DR.P3LocalOrbit

    nodePiece :
      H3Piece

    branchPiece :
      H3Piece

    nodePieceLocalizesToNode :
      localizedSector nodePiece ≡ DR.nodeOrbit

    branchPieceLocalizesToBranch :
      localizedSector branchPiece ≡ DR.branchOrbit

    everySectorHasSourcePiece :
      (sector : DR.P3LocalOrbit) ->
      H3Piece

    everySectorHasSourcePieceCorrect :
      (sector : DR.P3LocalOrbit) ->
      localizedSector (everySectorHasSourcePiece sector) ≡ sector

    normalizedDVRLength :
      H3Piece ->
      Nat

    localizedLengthMatchesSemistableMultiplicity :
      (piece : H3Piece) ->
      normalizedDVRLength piece
      ≡
      Geom.p3LocalGeometricMultiplicity (localizedSector piece)

    localizationDefinedWithoutMonsterResidual :
      Bool
    localizationDefinedWithoutMonsterResidualIsTrue :
      localizationDefinedWithoutMonsterResidual ≡ true

    localizationDefinedWithoutBase369Labels :
      Bool
    localizationDefinedWithoutBase369LabelsIsTrue :
      localizationDefinedWithoutBase369Labels ≡ true

open P3H3NodeBranchLocalizationTheorem public

------------------------------------------------------------------------
-- 2. Exact consequences of the theorem.
------------------------------------------------------------------------

nodeLengthIsOne :
  (T : P3H3NodeBranchLocalizationTheorem) ->
  normalizedDVRLength T (nodePiece T) ≡ 1
nodeLengthIsOne T =
  trans
    (localizedLengthMatchesSemistableMultiplicity T (nodePiece T))
    (cong Geom.p3LocalGeometricMultiplicity
      (nodePieceLocalizesToNode T))

branchLengthIsOne :
  (T : P3H3NodeBranchLocalizationTheorem) ->
  normalizedDVRLength T (branchPiece T) ≡ 1
branchLengthIsOne T =
  trans
    (localizedLengthMatchesSemistableMultiplicity T (branchPiece T))
    (cong Geom.p3LocalGeometricMultiplicity
      (branchPieceLocalizesToBranch T))

nodeAndBranchLengthSumIsTwo :
  (T : P3H3NodeBranchLocalizationTheorem) ->
  normalizedDVRLength T (nodePiece T)
  +
  normalizedDVRLength T (branchPiece T)
  ≡ 2
nodeAndBranchLengthSumIsTwo T
  rewrite nodeLengthIsOne T
        | branchLengthIsOne T =
  refl

------------------------------------------------------------------------
-- 3. Exact source receipt and unsupported-promotion firewalls.
------------------------------------------------------------------------

carnahanBoundary :
  Carnahan.ThreeBCarnahanOrderNineRefinementBoundary
carnahanBoundary =
  Carnahan.canonicalThreeBCarnahanOrderNineRefinementBoundary

data CarnahanReceiptAlreadyClassifiesNodeBranch : Set where
data CarnahanReceiptAlreadyProvesLengthOne : Set where
data TwoTotalDefinesLocalization : Set where
data Base369TritDefinesLocalization : Set where

carnahanReceiptDoesNotClassifyNodeBranch :
  CarnahanReceiptAlreadyClassifiesNodeBranch -> ⊥
carnahanReceiptDoesNotClassifyNodeBranch ()

carnahanReceiptDoesNotProveLengthOne :
  CarnahanReceiptAlreadyProvesLengthOne -> ⊥
carnahanReceiptDoesNotProveLengthOne ()

twoTotalDoesNotDefineLocalization :
  TwoTotalDefinesLocalization -> ⊥
twoTotalDoesNotDefineLocalization ()

base369TritDoesNotDefineLocalization :
  Base369TritDefinesLocalization -> ⊥
base369TritDoesNotDefineLocalization ()

------------------------------------------------------------------------
-- 4. Live wall.
------------------------------------------------------------------------

data P3H3NodeBranchLocalizationTheoremInhabited : Set where

p3H3NodeBranchLocalizationStillOpen :
  P3H3NodeBranchLocalizationTheoremInhabited -> ⊥
p3H3NodeBranchLocalizationStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record P3H3NodeBranchLocalizationBoundary : Set where
  constructor p3-h3-node-branch-localization-boundary
  field
    carnahanOrderNineDecompositionSourced : Bool
    carnahanFixedVectorEmbeddingSourced : Bool
    deligneRapoportTwoSectorGeometrySourced : Bool
    semistableMultiplicityOneOneOwned : Bool

    sourcePieceToNodeBranchFunctorRequired : Bool
    sourcePieceToNodeBranchFunctorInhabited : Bool
    sectorLengthOneOneAsSourceLengthRequired : Bool
    sectorLengthOneOneAsSourceLengthInhabited : Bool

    monsterResidualUsedToDefineLocalization : Bool
    base369UsedToDefineLocalization : Bool
    attributionFirewallPreserved : Bool

canonicalP3H3NodeBranchLocalizationBoundary :
  P3H3NodeBranchLocalizationBoundary
canonicalP3H3NodeBranchLocalizationBoundary =
  p3-h3-node-branch-localization-boundary
    true true true true
    true false true false
    false false true
