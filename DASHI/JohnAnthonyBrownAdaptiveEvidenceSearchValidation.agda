module DASHI.JohnAnthonyBrownAdaptiveEvidenceSearchValidation where

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownAdaptiveEvidenceSearchExact as Search
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest

johnAnthonyBrownAuthorPinned : Search.paperAuthor ≡ "John Anthony Brown"
johnAnthonyBrownAuthorPinned = refl

initialMoveIsExposureInstrument :
  Search.nextEvidenceMove Search.initialStage ≡
  Search.validateCoerciveExposureInstrument
initialMoveIsExposureInstrument = Search.initialNextMove

initialMoveIsHighestAlpha :
  Search.priorityTier Search.initialHighestAlphaMove ≡ Search.highestAlpha
initialMoveIsHighestAlpha = Search.initialHighestAlphaReallyHighest

exposureMoveFeedsH1 :
  Search.CandidateFor Search.validateCoerciveExposureInstrument Manifest.H1
exposureMoveFeedsH1 = Search.exposureForH1

exposureMoveFeedsH5 :
  Search.CandidateFor Search.validateCoerciveExposureInstrument Manifest.H5
exposureMoveFeedsH5 = Search.exposureForH5

betrayalMoveTargetsH3 :
  Search.CandidateFor Search.validateInstitutionalBetrayalMeasure Manifest.H3
betrayalMoveTargetsH3 = Search.betrayalForH3

confoundingMoveTargetsH5 :
  Search.CandidateFor Search.strengthenConfoundingModel Manifest.H5
confoundingMoveTargetsH5 = Search.confoundingForH5

selectionDoesNotAcquireEvidence : Search.SelectedMoveAcquiresEvidence → ⊥
selectionDoesNotAcquireEvidence = Search.selectionDoesNotAcquireEvidence

selectionDoesNotPromoteClaim : Search.SelectedMovePromotesHypothesis → ⊥
selectionDoesNotPromoteClaim = Search.selectionDoesNotPromoteHypothesis

costDoesNotEqualEthics : Search.LowestSearchCostEqualsBestEthics → ⊥
costDoesNotEqualEthics = Search.searchCostIsNotEthics

priorityDoesNotEqualTruth : Search.PlanningPriorityEqualsScientificTruth → ⊥
priorityDoesNotEqualTruth = Search.planningPriorityIsNotTruth

h3ForceRetained :
  Manifest.force Manifest.h3Manifest ≡ Manifest.incrementalPrediction
h3ForceRetained = Search.h3ConsumerStillIncremental

h5ForceRetained :
  Manifest.force Manifest.h5Manifest ≡ Manifest.adjustedAssociation
h5ForceRetained = Search.h5ConsumerStillAdjustedAssociation
