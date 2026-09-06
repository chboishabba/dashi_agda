module DASHI.Cognition.PNF.SensibLawMaboTwoOrderLandBackCausalCapstoneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboTwoOrderLandBackEverything as Base
import DASHI.Cognition.PNF.SensibLawMaboDawsonRadicalTitleRecognitionHingeExact as Hinge
import DASHI.Cognition.PNF.SensibLawLandBackIncomeProjectionNonFactorabilityExact as Income
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Recognition
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSocioeconomicModeratorHyperfabricExact as Moderator
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- Focused capstone for the two current residuals:
--   (1) CrownRadicalTitle -> ? -> DawsonRecognitionCondition
--   (2) LAND BACK component x governance condition -> outcome.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Doctrinal hinge/source status.
------------------------------------------------------------------------

dawsonRecognitionInferenceIsDirectPrimaryText :
  Hinge.sourceStatus Hinge.recognitionInferencePrimary ≡ Hinge.directPrimaryText
dawsonRecognitionInferenceIsDirectPrimaryText = refl

dawsonAcquiescenceEvidenceIsDirectPrimaryText :
  Hinge.sourceStatus Hinge.acquiescenceEvidencePrimary ≡ Hinge.directPrimaryText
dawsonAcquiescenceEvidenceIsDirectPrimaryText = refl

dawsonRadicalTitleRecognitionMediationIsStillUnresolved :
  Hinge.sourceStatus Hinge.radicalTitleRecognitionMediationCandidate ≡ Hinge.unresolvedBridge
dawsonRadicalTitleRecognitionMediationIsStillUnresolved = refl

dawsonHingeClosureStillOpen :
  Hinge.closure Hinge.currentDawsonHinge ≡ Hinge.unresolvedDoctrinalBridge
dawsonHingeClosureStillOpen = refl

dawsonRadicalTitleEntailmentNotProved :
  Hinge.radicalTitleEntailmentProved Hinge.currentDawsonHinge ≡ false
dawsonRadicalTitleEntailmentNotProved = refl

------------------------------------------------------------------------
-- Observer non-factorability: neither market income nor Crown recognition is a
-- sufficient statistic for the richer target state.
------------------------------------------------------------------------

cashIncomeNotSufficientForLandBackWellbeing :
  Income.cashIncomeIsSufficientStatisticForLandBackWellbeing
    Income.canonicalIncomeAdequacyBoundary ≡ false
cashIncomeNotSufficientForLandBackWellbeing = refl

lowerCashIncomeDoesNotFixRelationalWellbeing :
  Income.lowerCashIncomeProvesLowerRelationalWellbeing
    Income.canonicalIncomeAdequacyBoundary ≡ false
lowerCashIncomeDoesNotFixRelationalWellbeing = refl

crownRecognitionDoesNotExhaustCountryRelation :
  Recognition.crownRecognitionExhaustsCountryRelation
    Recognition.canonicalCrownRecognitionObserverBoundary ≡ false
crownRecognitionDoesNotExhaustCountryRelation = refl

crownRecognitionDoesNotExhaustCommunityAuthority :
  Recognition.crownRecognitionExhaustsCommunityAuthority
    Recognition.canonicalCrownRecognitionObserverBoundary ≡ false
crownRecognitionDoesNotExhaustCommunityAuthority = refl

------------------------------------------------------------------------
-- Source-authority constitution remains visible at the aggregate surface.
------------------------------------------------------------------------

usLandBackEconomicStudyRemainsWorkingPaper :
  Source.publicationStatus Source.arcoiteJohnson2025Authority
  ≡ Source.workingPaperNotPeerReviewed
usLandBackEconomicStudyRemainsWorkingPaper = refl

wriEconomicBenefitsRemainValuationEvidence :
  Source.authorityKind Source.wriTenureEconomicValuationAuthority
  ≡ Source.economicValuationReport
wriEconomicBenefitsRemainValuationEvidence = refl

amazon2024TradeoffStudyRemainsComparativeNotCausal :
  Source.authorityKind Source.denBraber2024Authority
  ≡ Source.peerReviewedComparativeStudy
amazon2024TradeoffStudyRemainsComparativeNotCausal = refl

------------------------------------------------------------------------
-- Refined socioeconomic state.
------------------------------------------------------------------------

coarseTradeoffLabelRejectedForDownstreamInference :
  Moderator.aggregateLabel Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.aggregateTradeoffLabelTooCoarse
coarseTradeoffLabelRejectedForDownstreamInference = refl

incomePenaltyIsComparatorSpecific :
  Moderator.incomeState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.incomePenaltyComparatorSpecific
incomePenaltyIsComparatorSpecific = refl

inequalityBenefitIsComparatorSpecific :
  Moderator.inequalityState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.inequalityBenefitComparatorSpecific
inequalityBenefitIsComparatorSpecific = refl

governanceModeratorStillRequiresIdentification :
  Moderator.moderatorState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.governanceModeratorIdentificationOpen
governanceModeratorStillRequiresIdentification = refl

extractivePressureIncomeMechanismIsHypothesisNotClosure :
  Moderator.status Moderator.extractivePressureIncomeInterpretationEdge
  ≡ Moderator.moderatorHypothesisOpen
extractivePressureIncomeMechanismIsHypothesisNotClosure = refl

------------------------------------------------------------------------
-- Two-order boundary remains the outer legal architecture.
------------------------------------------------------------------------

crownOrderStillDoesNotDetermineIndigenousOrderExistence :
  TwoOrder.courtDeterminesOrderExistence TwoOrder.indigenousOrderFibre ≡ false
crownOrderStillDoesNotDetermineIndigenousOrderExistence = refl

crownRecognitionStillDoesNotCreateIndigenousOrder :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
crownRecognitionStillDoesNotCreateIndigenousOrder = refl

------------------------------------------------------------------------
-- No-collapse exports.
------------------------------------------------------------------------

radicalTitleAloneDoesNotProveRecognitionCondition :
  Hinge.RadicalTitleAloneEntailsRecognitionCondition → ⊥
radicalTitleAloneDoesNotProveRecognitionCondition = Hinge.radicalTitleAloneDoesNotCloseHinge

recognitionEvidenceDoesNotProveConstitutiveCondition :
  Hinge.RecognitionEvidenceEntailsConstitutiveRecognitionCondition → ⊥
recognitionEvidenceDoesNotProveConstitutiveCondition = Hinge.recognitionEvidenceDoesNotEntailCondition

cashIncomeCannotFactorLandAuthority :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Income.cashIncomeObserver Income.landAuthorityOutcome → ⊥
cashIncomeCannotFactorLandAuthority = Income.cashIncomeDoesNotFactorLandAuthority

crownRecognitionCannotFactorIndigenousAuthority :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Recognition.crownRecognitionObserver Recognition.indigenousAuthorityOutcome → ⊥
crownRecognitionCannotFactorIndigenousAuthority = Recognition.crownRecognitionDoesNotFactorIndigenousAuthority

workingPaperDoesNotBecomePeerReviewedClosure :
  Source.WorkingPaperEqualsPeerReviewedResult → ⊥
workingPaperDoesNotBecomePeerReviewedClosure = Source.workingPaperDoesNotEqualPeerReview

subsidyAssociationDoesNotCloseIncomeMechanism :
  Moderator.SubsidyExposureExplainsDenBraberIncomeCoefficient → ⊥
subsidyAssociationDoesNotCloseIncomeMechanism = Moderator.subsidiesDoNotDirectlyExplainCoefficientYet

crossStudyDifferenceDoesNotProveGovernanceModerator :
  Moderator.GovernanceModeratorProvedByCrossStudyDifferenceAlone → ⊥
crossStudyDifferenceDoesNotProveGovernanceModerator = Moderator.crossStudyDifferenceDoesNotProveModerator
