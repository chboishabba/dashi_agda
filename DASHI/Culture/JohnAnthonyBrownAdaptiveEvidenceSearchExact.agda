module DASHI.Culture.JohnAnthonyBrownAdaptiveEvidenceSearchExact where

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN H1-H5 ADAPTIVE EVIDENCE SEARCH
--
-- Authorial source attribution:
--   John Anthony Brown
--
-- Purpose:
--   turn the existing H1-H5 manifest + selective reopening graph into a small
--   adaptive evidence-selection policy.  The policy ranks declared evidence
--   moves by consumer fan-out and a synthetic DASHI search-cost tier.
--
-- IMPORTANT:
--   the Nat scores below are planning fixtures only.  They are not empirical
--   effect sizes, study quality scores, monetary costs, ethical valuations, or
--   proof that one hypothesis is intrinsically more important than another.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest
import DASHI.Culture.JohnAnthonyBrownReceptionEvidenceReopeningBridgeExact as Brown

paperAuthor : String
paperAuthor = "John Anthony Brown"

------------------------------------------------------------------------
-- 1. Evidence-move language.
------------------------------------------------------------------------

data EvidenceMoveKind : Set where
  verifyPrimarySource
  validateInstrument
  recoverPopulationStudy
  reanalyseExistingData
  acquireNewMeasurement
  : EvidenceMoveKind

data EvidenceMove : Set where
  validateCoerciveExposureInstrument
  validateOutcomeVectorMeasures
  validateInstitutionalBetrayalMeasure
  validateModerationMeasures
  strengthenConfoundingModel
  recoverAutonomyReceptionSource
  recoverCatholicPopulationAssociation
  runTargetPopulationReplication
  : EvidenceMove

moveKind : EvidenceMove → EvidenceMoveKind
moveKind validateCoerciveExposureInstrument = validateInstrument
moveKind validateOutcomeVectorMeasures = validateInstrument
moveKind validateInstitutionalBetrayalMeasure = validateInstrument
moveKind validateModerationMeasures = validateInstrument
moveKind strengthenConfoundingModel = reanalyseExistingData
moveKind recoverAutonomyReceptionSource = verifyPrimarySource
moveKind recoverCatholicPopulationAssociation = recoverPopulationStudy
moveKind runTargetPopulationReplication = acquireNewMeasurement

moveTarget : EvidenceMove → Brown.BrownAuditArtifact
moveTarget validateCoerciveExposureInstrument = Brown.exposureMeasurementEvidence
moveTarget validateOutcomeVectorMeasures = Brown.outcomeMeasurementEvidence
moveTarget validateInstitutionalBetrayalMeasure = Brown.institutionalBetrayalMeasurementEvidence
moveTarget validateModerationMeasures = Brown.moderationMeasurementEvidence
moveTarget strengthenConfoundingModel = Brown.confoundingModelEvidence
moveTarget recoverAutonomyReceptionSource = Brown.conceptualReceptionEdge
moveTarget recoverCatholicPopulationAssociation = Brown.exposureMeasurementEvidence
moveTarget runTargetPopulationReplication = Brown.outcomeMeasurementEvidence

------------------------------------------------------------------------
-- 2. Consumer fan-out.
--
-- Count only the directly declared H1-H5 consumers in BrownDepends.  Rights /
-- policy and manuscript revision remain downstream and are not double-counted.
------------------------------------------------------------------------

directHypothesisFanout : EvidenceMove → Nat
directHypothesisFanout validateCoerciveExposureInstrument = 5
directHypothesisFanout validateOutcomeVectorMeasures = 4
directHypothesisFanout validateInstitutionalBetrayalMeasure = 1
directHypothesisFanout validateModerationMeasures = 1
directHypothesisFanout strengthenConfoundingModel = 2
directHypothesisFanout recoverAutonomyReceptionSource = 1
directHypothesisFanout recoverCatholicPopulationAssociation = 5
directHypothesisFanout runTargetPopulationReplication = 4

exposureInstrumentFanoutIsFive :
  directHypothesisFanout validateCoerciveExposureInstrument ≡ 5
exposureInstrumentFanoutIsFive = refl

confoundingFanoutIsTwo :
  directHypothesisFanout strengthenConfoundingModel ≡ 2
confoundingFanoutIsTwo = refl

------------------------------------------------------------------------
-- 3. Synthetic search/resource cost tier.
--
-- Lower is cheaper in this finite policy.  These values are deliberately NOT
-- claimed to represent real money, participant burden, ethics, calendar time,
-- statistical power or scientific value.
------------------------------------------------------------------------

searchCostTier : EvidenceMove → Nat
searchCostTier validateCoerciveExposureInstrument = 2
searchCostTier validateOutcomeVectorMeasures = 2
searchCostTier validateInstitutionalBetrayalMeasure = 1
searchCostTier validateModerationMeasures = 1
searchCostTier strengthenConfoundingModel = 1
searchCostTier recoverAutonomyReceptionSource = 1
searchCostTier recoverCatholicPopulationAssociation = 2
searchCostTier runTargetPopulationReplication = 4

------------------------------------------------------------------------
-- 4. Priority tier is a transparent ordinal planning code.
------------------------------------------------------------------------

data PriorityTier : Set where
  highestAlpha
  highAlpha
  mediumAlpha
  boundedAlpha
  : PriorityTier

priorityTier : EvidenceMove → PriorityTier
priorityTier validateCoerciveExposureInstrument = highestAlpha
priorityTier recoverCatholicPopulationAssociation = highestAlpha
priorityTier validateOutcomeVectorMeasures = highAlpha
priorityTier runTargetPopulationReplication = highAlpha
priorityTier strengthenConfoundingModel = mediumAlpha
priorityTier validateInstitutionalBetrayalMeasure = mediumAlpha
priorityTier validateModerationMeasures = boundedAlpha
priorityTier recoverAutonomyReceptionSource = boundedAlpha

initialHighestAlphaMove : EvidenceMove
initialHighestAlphaMove = validateCoerciveExposureInstrument

initialHighestAlphaReallyHighest :
  priorityTier initialHighestAlphaMove ≡ highestAlpha
initialHighestAlphaReallyHighest = refl

------------------------------------------------------------------------
-- 5. Adaptive continuation state.
--
-- Once one coordinate is provisionally resolved, do not keep selecting the same
-- move.  This is a finite policy specimen, not a claim that real research must
-- follow exactly this order.
------------------------------------------------------------------------

data EvidenceSearchStage : Set where
  initialStage
  exposureMeasureProvisionallyResolved
  outcomeMeasuresProvisionallyResolved
  confoundingModelProvisionallyResolved
  : EvidenceSearchStage

nextEvidenceMove : EvidenceSearchStage → EvidenceMove
nextEvidenceMove initialStage = validateCoerciveExposureInstrument
nextEvidenceMove exposureMeasureProvisionallyResolved = validateOutcomeVectorMeasures
nextEvidenceMove outcomeMeasuresProvisionallyResolved = strengthenConfoundingModel
nextEvidenceMove confoundingModelProvisionallyResolved = recoverCatholicPopulationAssociation

initialNextMove : nextEvidenceMove initialStage ≡ validateCoerciveExposureInstrument
initialNextMove = refl

afterExposureNextMove :
  nextEvidenceMove exposureMeasureProvisionallyResolved ≡ validateOutcomeVectorMeasures
afterExposureNextMove = refl

afterOutcomeNextMove :
  nextEvidenceMove outcomeMeasuresProvisionallyResolved ≡ strengthenConfoundingModel
afterOutcomeNextMove = refl

------------------------------------------------------------------------
-- 6. Claim-specific candidate menus.
------------------------------------------------------------------------

data CandidateFor : EvidenceMove → Manifest.HypothesisKey → Set where
  exposureForH1 : CandidateFor validateCoerciveExposureInstrument Manifest.H1
  exposureForH2 : CandidateFor validateCoerciveExposureInstrument Manifest.H2
  exposureForH3 : CandidateFor validateCoerciveExposureInstrument Manifest.H3
  exposureForH4 : CandidateFor validateCoerciveExposureInstrument Manifest.H4
  exposureForH5 : CandidateFor validateCoerciveExposureInstrument Manifest.H5

  outcomesForH1 : CandidateFor validateOutcomeVectorMeasures Manifest.H1
  outcomesForH2 : CandidateFor validateOutcomeVectorMeasures Manifest.H2
  outcomesForH4 : CandidateFor validateOutcomeVectorMeasures Manifest.H4
  outcomesForH5 : CandidateFor validateOutcomeVectorMeasures Manifest.H5

  betrayalForH3 : CandidateFor validateInstitutionalBetrayalMeasure Manifest.H3
  moderationForH4 : CandidateFor validateModerationMeasures Manifest.H4
  confoundingForH3 : CandidateFor strengthenConfoundingModel Manifest.H3
  confoundingForH5 : CandidateFor strengthenConfoundingModel Manifest.H5
  receptionForH2 : CandidateFor recoverAutonomyReceptionSource Manifest.H2

------------------------------------------------------------------------
-- 7. Selection does not acquire evidence or promote a hypothesis.
------------------------------------------------------------------------

data SelectedMoveAcquiresEvidence : Set where

data SelectedMovePromotesHypothesis : Set where

data HighestFanoutOverridesValidity : Set where

data LowestSearchCostEqualsBestEthics : Set where

data PlanningPriorityEqualsScientificTruth : Set where

selectionDoesNotAcquireEvidence : SelectedMoveAcquiresEvidence → ⊥
selectionDoesNotAcquireEvidence ()

selectionDoesNotPromoteHypothesis : SelectedMovePromotesHypothesis → ⊥
selectionDoesNotPromoteHypothesis ()

fanoutDoesNotOverrideValidity : HighestFanoutOverridesValidity → ⊥
fanoutDoesNotOverrideValidity ()

searchCostIsNotEthics : LowestSearchCostEqualsBestEthics → ⊥
searchCostIsNotEthics ()

planningPriorityIsNotTruth : PlanningPriorityEqualsScientificTruth → ⊥
planningPriorityIsNotTruth ()

------------------------------------------------------------------------
-- 8. Earlier-thread BIDI attribution and consumer boundaries.
------------------------------------------------------------------------

johnAnthonyBrownAttributionPinned : paperAuthor ≡ "John Anthony Brown"
johnAnthonyBrownAttributionPinned = refl

h1ConsumerStillAssociation :
  Manifest.force Manifest.h1Manifest ≡ Manifest.longitudinalAssociation
h1ConsumerStillAssociation = refl

h3ConsumerStillIncremental :
  Manifest.force Manifest.h3Manifest ≡ Manifest.incrementalPrediction
h3ConsumerStillIncremental = refl

h4ConsumerStillModeration :
  Manifest.force Manifest.h4Manifest ≡ Manifest.moderationInteraction
h4ConsumerStillModeration = refl

h5ConsumerStillAdjustedAssociation :
  Manifest.force Manifest.h5Manifest ≡ Manifest.adjustedAssociation
h5ConsumerStillAdjustedAssociation = refl

------------------------------------------------------------------------
-- 9. Boundary.
------------------------------------------------------------------------

record AdaptiveEvidenceSearchBoundary : Set where
  constructor adaptive-evidence-search-boundary
  field
    authorAttributedToJohnAnthonyBrown : Bool
    evidenceMovesAreConsumerRelative : Bool
    exposureMeasureHasWideDeclaredHypothesisFanout : Bool
    nextMoveMayChangeAfterEvidenceUpdate : Bool
    selectionEqualsEvidenceAcquisition : Bool
    selectionEqualsHypothesisPromotion : Bool
    fanoutOverridesMeasurementValidity : Bool
    searchCostIsWelfareOrEthicsMetric : Bool
    ordinalPriorityIsEmpiricalInformationGain : Bool
    draftAristotlePRImported : Bool

canonicalAdaptiveEvidenceSearchBoundary : AdaptiveEvidenceSearchBoundary
canonicalAdaptiveEvidenceSearchBoundary =
  adaptive-evidence-search-boundary
    true true true true false false false false false false
