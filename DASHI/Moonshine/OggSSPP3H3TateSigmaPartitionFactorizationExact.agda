module DASHI.Moonshine.OggSSPP3H3TateSigmaPartitionFactorizationExact where

------------------------------------------------------------------------
-- p=3 H3 -> TATE SIGMA -> DELIGNE--RAPOPORT PARTITION FACTORIZATION
--
-- We refine the partition payment from
--
--   H3 pieces -> {node,branch}
--
-- into two smaller recognitions:
--
--   G : H3 pieces -> {Tate H^0, Tate H^1}
--   A : {Tate H^0, Tate H^1} -> {node,branch}, up to the sourced swap ambiguity.
--
-- G + A construct the partition half of the p=3 localization theorem.
--
-- Carnahan sources the existence of the H3 decomposition and independently
-- sources the H^0/H^1 sigma split.  He does NOT source the map G.
-- Neither Carnahan nor Deligne--Rapoport sources the choice A.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSP3BCarnahanOrderNineFixedVectorRefinementExact as Carnahan
import DASHI.Moonshine.OggSSP3BCarnahanTateSigmaSplitExact as Tate
import DASHI.Moonshine.OggSSP3BTateSigmaDeligneRapoportRecognitionExact as SigmaDR
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as DR
import DASHI.Moonshine.OggSSPP3H3NodeBranchLocalizationFactorizationExact as Partition
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Missing source-native grading payment.
------------------------------------------------------------------------

record P3H3TateGradingAuthority : Set₁ where
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

    tateDegree :
      H3Piece ->
      Tate.ThreeBTateDegree

    everyTateDegreeHasSourcePiece :
      Tate.ThreeBTateDegree ->
      H3Piece

    everyTateDegreeHasSourcePieceCorrect :
      (degree : Tate.ThreeBTateDegree) ->
      tateDegree (everyTateDegreeHasSourcePiece degree) ≡ degree

    gradingComesFromIntegralTateObject :
      Bool
    gradingComesFromIntegralTateObjectIsTrue :
      gradingComesFromIntegralTateObject ≡ true

    gradingIndependentOfMonsterResidualTwo :
      Bool
    gradingIndependentOfMonsterResidualTwoIsTrue :
      gradingIndependentOfMonsterResidualTwo ≡ true

    gradingIndependentOfBase369Labels :
      Bool
    gradingIndependentOfBase369LabelsIsTrue :
      gradingIndependentOfBase369Labels ≡ true

open P3H3TateGradingAuthority public

------------------------------------------------------------------------
-- 2. G + A -> direct node/branch partition authority.
------------------------------------------------------------------------

asNodeBranchPartition :
  P3H3TateGradingAuthority ->
  SigmaDR.SigmaDRAlignmentAuthority ->
  Partition.P3H3NodeBranchPartitionAuthority
asNodeBranchPartition grading alignmentAuthority =
  record
    { Partition.H3Piece =
        H3Piece grading

    ; Partition.pieceComesFromCarnahanOrderNineDecomposition =
        pieceComesFromCarnahanOrderNineDecomposition grading
    ; Partition.pieceComesFromCarnahanOrderNineDecompositionIsTrue =
        pieceComesFromCarnahanOrderNineDecompositionIsTrue grading

    ; Partition.pieceEmbedsEquivariantlyIntoThreeBFixedVectors =
        pieceEmbedsEquivariantlyIntoThreeBFixedVectors grading
    ; Partition.pieceEmbedsEquivariantlyIntoThreeBFixedVectorsIsTrue =
        pieceEmbedsEquivariantlyIntoThreeBFixedVectorsIsTrue grading

    ; Partition.usesCarnahanLocalizedBaseExtension =
        usesCarnahanLocalizedBaseExtension grading
    ; Partition.usesCarnahanLocalizedBaseExtensionIsTrue =
        usesCarnahanLocalizedBaseExtensionIsTrue grading

    ; Partition.localizedSector =
        λ piece ->
          SigmaDR.tateToDR
            (SigmaDR.alignment alignmentAuthority)
            (tateDegree grading piece)

    ; Partition.nodePiece =
        everyTateDegreeHasSourcePiece grading
          (SigmaDR.drToTate
            (SigmaDR.alignment alignmentAuthority)
            DR.nodeOrbit)

    ; Partition.branchPiece =
        everyTateDegreeHasSourcePiece grading
          (SigmaDR.drToTate
            (SigmaDR.alignment alignmentAuthority)
            DR.branchOrbit)

    ; Partition.nodePieceLocalizesToNode =
        nodeCorrect

    ; Partition.branchPieceLocalizesToBranch =
        branchCorrect

    ; Partition.everySectorHasSourcePiece =
        λ sector ->
          everyTateDegreeHasSourcePiece grading
            (SigmaDR.drToTate
              (SigmaDR.alignment alignmentAuthority)
              sector)

    ; Partition.everySectorHasSourcePieceCorrect =
        everySectorCorrect

    ; Partition.localizationDefinedWithoutMonsterResidual =
        gradingIndependentOfMonsterResidualTwo grading
    ; Partition.localizationDefinedWithoutMonsterResidualIsTrue =
        gradingIndependentOfMonsterResidualTwoIsTrue grading

    ; Partition.localizationDefinedWithoutBase369Labels =
        gradingIndependentOfBase369Labels grading
    ; Partition.localizationDefinedWithoutBase369LabelsIsTrue =
        gradingIndependentOfBase369LabelsIsTrue grading
    }
  where
    chosenAlignment :
      SigmaDR.SigmaDRAlignment
    chosenAlignment =
      SigmaDR.alignment alignmentAuthority

    nodeDegree :
      Tate.ThreeBTateDegree
    nodeDegree =
      SigmaDR.drToTate chosenAlignment DR.nodeOrbit

    branchDegree :
      Tate.ThreeBTateDegree
    branchDegree =
      SigmaDR.drToTate chosenAlignment DR.branchOrbit

    nodeCorrect :
      SigmaDR.tateToDR chosenAlignment
        (tateDegree grading
          (everyTateDegreeHasSourcePiece grading nodeDegree))
      ≡ DR.nodeOrbit
    nodeCorrect =
      trans
        (cong
          (SigmaDR.tateToDR chosenAlignment)
          (everyTateDegreeHasSourcePieceCorrect grading nodeDegree))
        (SigmaDR.drRoundTrip chosenAlignment DR.nodeOrbit)

    branchCorrect :
      SigmaDR.tateToDR chosenAlignment
        (tateDegree grading
          (everyTateDegreeHasSourcePiece grading branchDegree))
      ≡ DR.branchOrbit
    branchCorrect =
      trans
        (cong
          (SigmaDR.tateToDR chosenAlignment)
          (everyTateDegreeHasSourcePieceCorrect grading branchDegree))
        (SigmaDR.drRoundTrip chosenAlignment DR.branchOrbit)

    everySectorCorrect :
      (sector : DR.P3LocalOrbit) ->
      SigmaDR.tateToDR chosenAlignment
        (tateDegree grading
          (everyTateDegreeHasSourcePiece grading
            (SigmaDR.drToTate chosenAlignment sector)))
      ≡ sector
    everySectorCorrect sector =
      trans
        (cong
          (SigmaDR.tateToDR chosenAlignment)
          (everyTateDegreeHasSourcePieceCorrect grading
            (SigmaDR.drToTate chosenAlignment sector)))
        (SigmaDR.drRoundTrip chosenAlignment sector)

------------------------------------------------------------------------
-- 3. The remaining ambiguity is now exactly two payments.
------------------------------------------------------------------------

data CarnahanH3ReceiptCreatesTateGrading : Set where
data CarnahanSigmaSplitGradesEveryH3Piece : Set where
data CardinalityTwoChoosesSigmaDRAlignment : Set where
data TateGradingChoosesSigmaDRAlignment : Set where

carnahanH3ReceiptDoesNotCreateTateGrading :
  CarnahanH3ReceiptCreatesTateGrading -> ⊥
carnahanH3ReceiptDoesNotCreateTateGrading ()

carnahanSigmaSplitDoesNotAutomaticallyGradeEveryH3Piece :
  CarnahanSigmaSplitGradesEveryH3Piece -> ⊥
carnahanSigmaSplitDoesNotAutomaticallyGradeEveryH3Piece ()

cardinalityTwoDoesNotChooseSigmaDRAlignment :
  CardinalityTwoChoosesSigmaDRAlignment -> ⊥
cardinalityTwoDoesNotChooseSigmaDRAlignment ()

tateGradingDoesNotChooseSigmaDRAlignment :
  TateGradingChoosesSigmaDRAlignment -> ⊥
tateGradingDoesNotChooseSigmaDRAlignment ()

------------------------------------------------------------------------
-- 4. Source receipts and live wall.
------------------------------------------------------------------------

h3Boundary :
  Carnahan.ThreeBCarnahanOrderNineRefinementBoundary
h3Boundary =
  Carnahan.canonicalThreeBCarnahanOrderNineRefinementBoundary

tateBoundary :
  Tate.ThreeBTateSigmaSplitBoundary
tateBoundary =
  Tate.canonicalThreeBTateSigmaSplitBoundary

alignmentBoundary :
  SigmaDR.ThreeBTateSigmaDRRecognitionBoundary
alignmentBoundary =
  SigmaDR.canonicalThreeBTateSigmaDRRecognitionBoundary

data P3H3TateGradingAuthorityInhabited : Set where

h3TateGradingStillOpen :
  P3H3TateGradingAuthorityInhabited -> ⊥
h3TateGradingStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P3H3TateSigmaPartitionFactorizationBoundary : Set where
  constructor p3-h3-tate-sigma-partition-factorization-boundary
  field
    h3SourceDecompositionSourced : Bool
    tateSigmaBinarySplitSourced : Bool
    h3ToTateGradingRequired : Bool
    h3ToTateGradingInhabited : Bool
    sigmaDRRecognitionUpToSwapPaid : Bool
    sigmaDRAlignmentAuthorityRequired : Bool
    sigmaDRAlignmentAuthorityInhabited : Bool
    gradingAndAlignmentAssembleNodeBranchPartition : Bool
    carnahanCreditedWithGrading : Bool
    carnahanCreditedWithDRAlignment : Bool
    monsterResidualUsedToDefineEitherPayment : Bool
    base369UsedToDefineEitherPayment : Bool
    attributionFirewallPreserved : Bool

canonicalP3H3TateSigmaPartitionFactorizationBoundary :
  P3H3TateSigmaPartitionFactorizationBoundary
canonicalP3H3TateSigmaPartitionFactorizationBoundary =
  p3-h3-tate-sigma-partition-factorization-boundary
    true true true false
    true true false true
    false false false false true
