module DASHI.Physics.QFT.GluonSectorFromDepth2Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Depth-2 / gluon-sector investigation receipt.
--
-- This module records the local bookkeeping check requested for the
-- spin-1, depth-2 candidate obtained by trying a naive tensor-product
-- dimension count on the finite CM lanes.  The count
--
--   4^2 + 6^2 + 2^2 - 1 = 55
--
-- is recorded as an investigated candidate surface only.  It is not the
-- SU(3) adjoint dimension 8, so no gluon-sector match or exact Standard
-- Model promotion is claimed here.

data Depth2GluonSectorStatus : Set where
  depth2CandidateInvestigatedNoPromotion :
    Depth2GluonSectorStatus

data Depth2GluonCandidateBlocker : Set where
  naiveDimensionNotSU3Adjoint :
    Depth2GluonCandidateBlocker

  missingSU3AdjointExtraction :
    Depth2GluonCandidateBlocker

  missingDHRGluonSectorConstruction :
    Depth2GluonCandidateBlocker

  missingExactStandardModelGaugePromotion :
    Depth2GluonCandidateBlocker

canonicalDepth2GluonCandidateBlockers :
  List Depth2GluonCandidateBlocker
canonicalDepth2GluonCandidateBlockers =
  naiveDimensionNotSU3Adjoint
  ∷ missingSU3AdjointExtraction
  ∷ missingDHRGluonSectorConstruction
  ∷ missingExactStandardModelGaugePromotion
  ∷ []

spinOneDepthTwoCandidateLabel : String
spinOneDepthTwoCandidateLabel =
  "spin-1 depth-2 gluon-sector candidate"

naiveDepth2TensorProductDimensionExpressionLabel : String
naiveDepth2TensorProductDimensionExpressionLabel =
  "4^2 + 6^2 + 2^2 - 1"

su3AdjointDimensionLabel : String
su3AdjointDimensionLabel =
  "SU3 adjoint dimension"

naiveDepth2DimensionMismatchLabel : String
naiveDepth2DimensionMismatchLabel =
  "The naive depth-2 tensor-product dimension is 55, not the SU3 adjoint dimension 8"

naiveDepth2DimensionExpression :
  Nat
naiveDepth2DimensionExpression =
  (4 * 4) + (6 * 6) + (2 * 2) - 1

naiveDepth2DimensionExpressionComputesTo55 :
  naiveDepth2DimensionExpression ≡ 55
naiveDepth2DimensionExpressionComputesTo55 =
  refl

record SpinOneDepthTwoGluonSectorCandidate : Setω where
  field
    candidateLabel :
      String

    candidateLabelIsCanonical :
      candidateLabel ≡ spinOneDepthTwoCandidateLabel

    candidateSpin :
      Nat

    candidateSpinIsOne :
      candidateSpin ≡ 1

    candidateDepth :
      Nat

    candidateDepthIsTwo :
      candidateDepth ≡ 2

    candidateIsSpinOneDepthTwo :
      Bool

    candidateIsSpinOneDepthTwoIsTrue :
      candidateIsSpinOneDepthTwo ≡ true

    depth2TensorProductStructureInvestigated :
      Bool

    depth2TensorProductStructureInvestigatedIsTrue :
      depth2TensorProductStructureInvestigated ≡ true

    dimensionExpressionLabel :
      String

    dimensionExpressionLabelIsCanonical :
      dimensionExpressionLabel
      ≡
      naiveDepth2TensorProductDimensionExpressionLabel

    naiveDimensionFromExpression :
      Nat

    naiveDimensionFromExpressionIsExpression :
      naiveDimensionFromExpression ≡ naiveDepth2DimensionExpression

    naiveDimensionFromExpressionIsFiftyFive :
      naiveDimensionFromExpression ≡ 55

open SpinOneDepthTwoGluonSectorCandidate public

canonicalSpinOneDepthTwoGluonSectorCandidate :
  SpinOneDepthTwoGluonSectorCandidate
canonicalSpinOneDepthTwoGluonSectorCandidate =
  record
    { candidateLabel =
        spinOneDepthTwoCandidateLabel
    ; candidateLabelIsCanonical =
        refl
    ; candidateSpin =
        1
    ; candidateSpinIsOne =
        refl
    ; candidateDepth =
        2
    ; candidateDepthIsTwo =
        refl
    ; candidateIsSpinOneDepthTwo =
        true
    ; candidateIsSpinOneDepthTwoIsTrue =
        refl
    ; depth2TensorProductStructureInvestigated =
        true
    ; depth2TensorProductStructureInvestigatedIsTrue =
        refl
    ; dimensionExpressionLabel =
        naiveDepth2TensorProductDimensionExpressionLabel
    ; dimensionExpressionLabelIsCanonical =
        refl
    ; naiveDimensionFromExpression =
        naiveDepth2DimensionExpression
    ; naiveDimensionFromExpressionIsExpression =
        refl
    ; naiveDimensionFromExpressionIsFiftyFive =
        refl
    }

record GluonSectorFromDepth2Receipt : Setω where
  field
    status :
      Depth2GluonSectorStatus

    statusIsInvestigatedNoPromotion :
      status ≡ depth2CandidateInvestigatedNoPromotion

    spinOneDepthTwoCandidate :
      SpinOneDepthTwoGluonSectorCandidate

    spinOneDepthTwoCandidateCanonicalSelected :
      Bool

    spinOneDepthTwoCandidateCanonicalSelectedIsTrue :
      spinOneDepthTwoCandidateCanonicalSelected ≡ true

    depth2TensorProductStructureInvestigated :
      Bool

    depth2TensorProductStructureInvestigatedIsTrue :
      depth2TensorProductStructureInvestigated ≡ true

    naiveDepth2Dimension :
      Nat

    naiveDepth2DimensionIsFiftyFive :
      naiveDepth2Dimension ≡ 55

    naiveDepth2DimensionIsExpression :
      naiveDepth2Dimension
      ≡
      (4 * 4) + (6 * 6) + (2 * 2) - 1

    su3AdjointDimension :
      Nat

    su3AdjointDimensionIsEight :
      su3AdjointDimension ≡ 8

    su3AdjointDimensionMeaning :
      String

    su3AdjointDimensionMeaningIsCanonical :
      su3AdjointDimensionMeaning ≡ su3AdjointDimensionLabel

    naiveDepth2GluonMatch :
      Bool

    naiveDepth2GluonMatchIsFalse :
      naiveDepth2GluonMatch ≡ false

    gluonSectorCandidateOpen :
      Bool

    gluonSectorCandidateOpenIsTrue :
      gluonSectorCandidateOpen ≡ true

    exactStandardModelReconstruction :
      Bool

    exactStandardModelReconstructionIsFalse :
      exactStandardModelReconstruction ≡ false

    mismatchBoundary :
      String

    mismatchBoundaryIsCanonical :
      mismatchBoundary ≡ naiveDepth2DimensionMismatchLabel

    blockers :
      List Depth2GluonCandidateBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDepth2GluonCandidateBlockers

    receiptBoundary :
      List String

open GluonSectorFromDepth2Receipt public

canonicalGluonSectorFromDepth2Receipt :
  GluonSectorFromDepth2Receipt
canonicalGluonSectorFromDepth2Receipt =
  record
    { status =
        depth2CandidateInvestigatedNoPromotion
    ; statusIsInvestigatedNoPromotion =
        refl
    ; spinOneDepthTwoCandidate =
        canonicalSpinOneDepthTwoGluonSectorCandidate
    ; spinOneDepthTwoCandidateCanonicalSelected =
        true
    ; spinOneDepthTwoCandidateCanonicalSelectedIsTrue =
        refl
    ; depth2TensorProductStructureInvestigated =
        true
    ; depth2TensorProductStructureInvestigatedIsTrue =
        refl
    ; naiveDepth2Dimension =
        55
    ; naiveDepth2DimensionIsFiftyFive =
        refl
    ; naiveDepth2DimensionIsExpression =
        refl
    ; su3AdjointDimension =
        8
    ; su3AdjointDimensionIsEight =
        refl
    ; su3AdjointDimensionMeaning =
        su3AdjointDimensionLabel
    ; su3AdjointDimensionMeaningIsCanonical =
        refl
    ; naiveDepth2GluonMatch =
        false
    ; naiveDepth2GluonMatchIsFalse =
        refl
    ; gluonSectorCandidateOpen =
        true
    ; gluonSectorCandidateOpenIsTrue =
        refl
    ; exactStandardModelReconstruction =
        false
    ; exactStandardModelReconstructionIsFalse =
        refl
    ; mismatchBoundary =
        naiveDepth2DimensionMismatchLabel
    ; mismatchBoundaryIsCanonical =
        refl
    ; blockers =
        canonicalDepth2GluonCandidateBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "The depth-2 tensor-product structure has been investigated for a spin-1 candidate"
        ∷ "The naive dimension expression 4^2 + 6^2 + 2^2 - 1 computes to 55"
        ∷ "The SU3 adjoint dimension is 8, so the naive depth-2 gluon match is false"
        ∷ "The gluon-sector candidate remains open, with exact Standard Model reconstruction false"
        ∷ []
    }

depth2TensorProductStructureInvestigatedRecorded :
  GluonSectorFromDepth2Receipt.depth2TensorProductStructureInvestigated
    canonicalGluonSectorFromDepth2Receipt
  ≡
  true
depth2TensorProductStructureInvestigatedRecorded =
  GluonSectorFromDepth2Receipt.depth2TensorProductStructureInvestigatedIsTrue
    canonicalGluonSectorFromDepth2Receipt

naiveDepth2DimensionRecordedAsFiftyFive :
  GluonSectorFromDepth2Receipt.naiveDepth2Dimension
    canonicalGluonSectorFromDepth2Receipt
  ≡
  55
naiveDepth2DimensionRecordedAsFiftyFive =
  GluonSectorFromDepth2Receipt.naiveDepth2DimensionIsFiftyFive
    canonicalGluonSectorFromDepth2Receipt

su3AdjointDimensionRecordedAsEight :
  GluonSectorFromDepth2Receipt.su3AdjointDimension
    canonicalGluonSectorFromDepth2Receipt
  ≡
  8
su3AdjointDimensionRecordedAsEight =
  GluonSectorFromDepth2Receipt.su3AdjointDimensionIsEight
    canonicalGluonSectorFromDepth2Receipt

naiveDepth2GluonMatchRecordedFalse :
  GluonSectorFromDepth2Receipt.naiveDepth2GluonMatch
    canonicalGluonSectorFromDepth2Receipt
  ≡
  false
naiveDepth2GluonMatchRecordedFalse =
  GluonSectorFromDepth2Receipt.naiveDepth2GluonMatchIsFalse
    canonicalGluonSectorFromDepth2Receipt

gluonSectorCandidateOpenRecordedTrue :
  GluonSectorFromDepth2Receipt.gluonSectorCandidateOpen
    canonicalGluonSectorFromDepth2Receipt
  ≡
  true
gluonSectorCandidateOpenRecordedTrue =
  GluonSectorFromDepth2Receipt.gluonSectorCandidateOpenIsTrue
    canonicalGluonSectorFromDepth2Receipt

exactStandardModelReconstructionRecordedFalse :
  GluonSectorFromDepth2Receipt.exactStandardModelReconstruction
    canonicalGluonSectorFromDepth2Receipt
  ≡
  false
exactStandardModelReconstructionRecordedFalse =
  GluonSectorFromDepth2Receipt.exactStandardModelReconstructionIsFalse
    canonicalGluonSectorFromDepth2Receipt
