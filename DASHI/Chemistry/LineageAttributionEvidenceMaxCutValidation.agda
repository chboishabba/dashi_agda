module DASHI.Chemistry.LineageAttributionEvidenceMaxCutValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Chemistry.LineageAttributionEvidenceSourceAtlasExact as Sources
import DASHI.Chemistry.LineageAttributionEvidencePaymentExact as Payment
import DASHI.Chemistry.AttributedGoldReactionReplayExact as Replay
import DASHI.Chemistry.LineageQuantitativeCalibrationLedgerExact as Calibration
import DASHI.Chemistry.LineageAttributionAcquisitionFrontierExact as Pareto

sourceAtlasDoesNotCreateAuthority :
  Sources.atlasCreatesAuthority Sources.canonicalLineageCalibrationSourceAtlas ≡ false
sourceAtlasDoesNotCreateAuthority = refl

externalAndDASHISynthesisRemainDistinct :
  Payment.externalResultEqualsDASHISynthesis Payment.canonicalLineageAttributionBoundary ≡ false
  × Payment.dashiCompositionTransfersToSource Payment.canonicalLineageAttributionBoundary ≡ false
externalAndDASHISynthesisRemainDistinct = refl , refl

citationDoesNotPromoteCalibration :
  Payment.citationAlonePaysCalibration Payment.canonicalLineageAttributionBoundary ≡ false
citationDoesNotPromoteCalibration = refl

primarySecondaryAndDatabaseRolesStayTyped :
  Payment.sourceRoleCollapsed Payment.canonicalLineageAttributionBoundary ≡ false
primarySecondaryAndDatabaseRolesStayTyped = refl

unpaidCoordinatesRemainUnpaid :
  Payment.missingCoordinatePromotedByNearbyCitation Payment.canonicalLineageAttributionBoundary ≡ false
unpaidCoordinatesRemainUnpaid = refl

attributedReplayKeepsExternalAndDASHIOwnershipSeparate :
  Replay.sourceOwnsReplayComposition Replay.canonicalAttributedGoldReplayBoundary ≡ false
  × Replay.replayCompositionErasesSourceIdentity Replay.canonicalAttributedGoldReplayBoundary ≡ false
attributedReplayKeepsExternalAndDASHIOwnershipSeparate = refl , refl

numericPromotionNeedsExactLocatorAndContext :
  Calibration.numberWithoutExactLocatorPromoted Calibration.canonicalQuantitativeCalibrationBoundary ≡ false
  × Calibration.numberWithoutContextPromoted Calibration.canonicalQuantitativeCalibrationBoundary ≡ false
numericPromotionNeedsExactLocatorAndContext = refl , refl

unpaidNumericCellsAreNotZeroes :
  Calibration.unpaidCoordinateInterpretedAsZero Calibration.canonicalQuantitativeCalibrationBoundary ≡ false
unpaidNumericCellsAreNotZeroes = refl

paretoAcquisitionIsNotTruthRanking :
  Pareto.frontierRankIsTruthRank Pareto.canonicalLineageAttributionAcquisitionFrontier ≡ false
  × Pareto.acquisitionCreatesAuthority Pareto.canonicalLineageAttributionAcquisitionFrontier ≡ false
paretoAcquisitionIsNotTruthRanking = refl , refl
