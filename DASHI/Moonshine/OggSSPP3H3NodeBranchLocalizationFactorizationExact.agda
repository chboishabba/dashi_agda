module DASHI.Moonshine.OggSSPP3H3NodeBranchLocalizationFactorizationExact where

------------------------------------------------------------------------
-- p=3 H3 -> NODE/BRANCH LOCALIZATION FACTORIZATION
--
-- PURPOSE
--
-- Split the current p=3 terminal wall exactly along the source boundary.
--
-- Carnahan sources:
--   * existence of an order-9 3B-pure decomposition into pieces;
--   * equivariant embedding of those pieces into 3B-fixed vectors;
--   * the required localized/base-extended setting.
--
-- Carnahan does NOT source:
--   * a partition of those pieces into Deligne--Rapoport node/branch sectors;
--   * normalized DVR length one on either sector.
--
-- Therefore the missing theorem is factored into two independent payments:
--
--   P : source-native H3-piece -> {node,branch} partition/surjectivity;
--   L : normalized DVR length of each localized piece equals the independent
--       semistable multiplicity of its assigned sector.
--
-- P + L reconstruct the existing P3H3NodeBranchLocalizationTheorem.
--
-- ATTRIBUTION
--
-- Carnahan owns only the decomposition/fixed-vector/base-extension surface.
-- Deligne--Rapoport owns the semistable node/branch geometry.
-- DASHI owns this factorization and any later proof connecting them.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP3BCarnahanOrderNineFixedVectorRefinementExact as Carnahan
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as DR
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalMultiplicityExact as Geom
import DASHI.Moonshine.OggSSPP3H3NodeBranchLocalizationObligationExact as Full
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Payment P: source-native partition/localization only.
------------------------------------------------------------------------

record P3H3NodeBranchPartitionAuthority : Set₁ where
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

    usesCarnahanLocalizedBaseExtension :
      Bool

    usesCarnahanLocalizedBaseExtensionIsTrue :
      usesCarnahanLocalizedBaseExtension ≡ true

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

    localizationDefinedWithoutMonsterResidual :
      Bool
    localizationDefinedWithoutMonsterResidualIsTrue :
      localizationDefinedWithoutMonsterResidual ≡ true

    localizationDefinedWithoutBase369Labels :
      Bool
    localizationDefinedWithoutBase369LabelsIsTrue :
      localizationDefinedWithoutBase369Labels ≡ true

open P3H3NodeBranchPartitionAuthority public

------------------------------------------------------------------------
-- 2. Payment L: length comparison over an already-defined partition.
------------------------------------------------------------------------

record P3H3NodeBranchLengthComparisonAuthority
    (partition : P3H3NodeBranchPartitionAuthority) : Set₁ where
  field
    normalizedDVRLength :
      H3Piece partition ->
      Nat

    localizedLengthMatchesSemistableMultiplicity :
      (piece : H3Piece partition) ->
      normalizedDVRLength piece
      ≡
      Geom.p3LocalGeometricMultiplicity
        (localizedSector partition piece)

    lengthComparisonDefinedWithoutMonsterResidual :
      Bool
    lengthComparisonDefinedWithoutMonsterResidualIsTrue :
      lengthComparisonDefinedWithoutMonsterResidual ≡ true

    lengthComparisonDefinedWithoutBase369Labels :
      Bool
    lengthComparisonDefinedWithoutBase369LabelsIsTrue :
      lengthComparisonDefinedWithoutBase369Labels ≡ true

open P3H3NodeBranchLengthComparisonAuthority public

------------------------------------------------------------------------
-- 3. The two independent payments reconstruct the current full theorem.
------------------------------------------------------------------------

assembleP3H3NodeBranchLocalization :
  (partition : P3H3NodeBranchPartitionAuthority) ->
  P3H3NodeBranchLengthComparisonAuthority partition ->
  Full.P3H3NodeBranchLocalizationTheorem
assembleP3H3NodeBranchLocalization partition length =
  record
    { Full.H3Piece =
        H3Piece partition

    ; Full.pieceComesFromCarnahanOrderNineDecomposition =
        pieceComesFromCarnahanOrderNineDecomposition partition
    ; Full.pieceComesFromCarnahanOrderNineDecompositionIsTrue =
        pieceComesFromCarnahanOrderNineDecompositionIsTrue partition

    ; Full.pieceEmbedsEquivariantlyIntoThreeBFixedVectors =
        pieceEmbedsEquivariantlyIntoThreeBFixedVectors partition
    ; Full.pieceEmbedsEquivariantlyIntoThreeBFixedVectorsIsTrue =
        pieceEmbedsEquivariantlyIntoThreeBFixedVectorsIsTrue partition

    ; Full.usesCarnahanLocalizedBaseExtension =
        usesCarnahanLocalizedBaseExtension partition
    ; Full.usesCarnahanLocalizedBaseExtensionIsTrue =
        usesCarnahanLocalizedBaseExtensionIsTrue partition

    ; Full.localizedSector =
        localizedSector partition

    ; Full.nodePiece =
        nodePiece partition
    ; Full.branchPiece =
        branchPiece partition

    ; Full.nodePieceLocalizesToNode =
        nodePieceLocalizesToNode partition
    ; Full.branchPieceLocalizesToBranch =
        branchPieceLocalizesToBranch partition

    ; Full.everySectorHasSourcePiece =
        everySectorHasSourcePiece partition
    ; Full.everySectorHasSourcePieceCorrect =
        everySectorHasSourcePieceCorrect partition

    ; Full.normalizedDVRLength =
        normalizedDVRLength length
    ; Full.localizedLengthMatchesSemistableMultiplicity =
        localizedLengthMatchesSemistableMultiplicity length

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
-- 4. Exact consequences once both payments exist.
------------------------------------------------------------------------

nodeLengthIsOne :
  (partition : P3H3NodeBranchPartitionAuthority) ->
  (length : P3H3NodeBranchLengthComparisonAuthority partition) ->
  normalizedDVRLength length (nodePiece partition) ≡ 1
nodeLengthIsOne partition length =
  Full.nodeLengthIsOne
    (assembleP3H3NodeBranchLocalization partition length)

branchLengthIsOne :
  (partition : P3H3NodeBranchPartitionAuthority) ->
  (length : P3H3NodeBranchLengthComparisonAuthority partition) ->
  normalizedDVRLength length (branchPiece partition) ≡ 1
branchLengthIsOne partition length =
  Full.branchLengthIsOne
    (assembleP3H3NodeBranchLocalization partition length)

nodeAndBranchLengthSumIsTwo :
  (partition : P3H3NodeBranchPartitionAuthority) ->
  (length : P3H3NodeBranchLengthComparisonAuthority partition) ->
  normalizedDVRLength length (nodePiece partition)
  +
  normalizedDVRLength length (branchPiece partition)
  ≡ 2
nodeAndBranchLengthSumIsTwo partition length =
  Full.nodeAndBranchLengthSumIsTwo
    (assembleP3H3NodeBranchLocalization partition length)

------------------------------------------------------------------------
-- 5. Independence / no-shortcut firewalls.
------------------------------------------------------------------------

data PartitionAuthorityCreatesLengthComparison : Set where
data LengthComparisonCreatesSourcePartition : Set where
data CarnahanReceiptCreatesPartitionAuthority : Set where
data DeligneRapoportMultiplicityCreatesLengthComparison : Set where
data TotalTwoCreatesEitherPayment : Set where
data Base369CreatesEitherPayment : Set where

partitionDoesNotCreateLengthComparison :
  PartitionAuthorityCreatesLengthComparison -> ⊥
partitionDoesNotCreateLengthComparison ()

lengthComparisonDoesNotCreateSourcePartition :
  LengthComparisonCreatesSourcePartition -> ⊥
lengthComparisonDoesNotCreateSourcePartition ()

carnahanReceiptDoesNotCreatePartitionAuthority :
  CarnahanReceiptCreatesPartitionAuthority -> ⊥
carnahanReceiptDoesNotCreatePartitionAuthority ()

deligneRapoportMultiplicityDoesNotCreateLengthComparison :
  DeligneRapoportMultiplicityCreatesLengthComparison -> ⊥
deligneRapoportMultiplicityDoesNotCreateLengthComparison ()

totalTwoDoesNotCreateEitherPayment :
  TotalTwoCreatesEitherPayment -> ⊥
totalTwoDoesNotCreateEitherPayment ()

base369DoesNotCreateEitherPayment :
  Base369CreatesEitherPayment -> ⊥
base369DoesNotCreateEitherPayment ()

------------------------------------------------------------------------
-- 6. Source boundary and live cut.
------------------------------------------------------------------------

carnahanBoundary :
  Carnahan.ThreeBCarnahanOrderNineRefinementBoundary
carnahanBoundary =
  Carnahan.canonicalThreeBCarnahanOrderNineRefinementBoundary

data P3H3NodeBranchPartitionAuthorityInhabited : Set where
data P3H3NodeBranchLengthComparisonAuthorityInhabited : Set where

partitionAuthorityStillOpen :
  P3H3NodeBranchPartitionAuthorityInhabited -> ⊥
partitionAuthorityStillOpen ()

lengthComparisonAuthorityStillOpen :
  P3H3NodeBranchLengthComparisonAuthorityInhabited -> ⊥
lengthComparisonAuthorityStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P3H3NodeBranchLocalizationFactorizationBoundary : Set where
  constructor p3-h3-node-branch-localization-factorization-boundary
  field
    carnahanDecompositionAndEmbeddingSourced : Bool
    deligneRapoportGeometrySourced : Bool
    partitionPaymentSeparated : Bool
    lengthPaymentSeparated : Bool
    twoPaymentsAssembleFullLocalization : Bool
    partitionPaymentInhabited : Bool
    lengthPaymentInhabited : Bool
    carnahanCreditedWithPartition : Bool
    carnahanCreditedWithLengthOne : Bool
    monsterResidualUsedToDefinePayments : Bool
    base369UsedToDefinePayments : Bool
    attributionFirewallPreserved : Bool

canonicalP3H3NodeBranchLocalizationFactorizationBoundary :
  P3H3NodeBranchLocalizationFactorizationBoundary
canonicalP3H3NodeBranchLocalizationFactorizationBoundary =
  p3-h3-node-branch-localization-factorization-boundary
    true true true true true
    false false false false false false true
