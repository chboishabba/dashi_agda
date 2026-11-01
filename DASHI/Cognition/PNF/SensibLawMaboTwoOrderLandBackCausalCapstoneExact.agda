module DASHI.Cognition.PNF.SensibLawMaboTwoOrderLandBackCausalCapstoneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawMaboTwoOrderLandBackEverything as Base
import DASHI.Cognition.PNF.SensibLawMaboDawsonRadicalTitleRecognitionHingeExact as Hinge
import DASHI.Cognition.PNF.SensibLawLandBackIncomeProjectionNonFactorabilityExact as Income
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Recognition
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueProjectionNonFactorabilityExact as CarbonProjection
import DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueComparabilityExact as CarbonValue
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSocioeconomicModeratorHyperfabricExact as Moderator
import DASHI.Cognition.PNF.SensibLawLandBackEvidenceDesignCorrectionExact as DesignCorrection
import DASHI.Cognition.PNF.SensibLawMaboLandBackSourceAttributionAuditExact as Audit
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- Focused capstone for the two current residuals:
--   (1) CrownRadicalTitle -> ? -> DawsonRecognitionCondition
--   (2) LAND BACK component x governance x market/subsidy context x observer
--       -> outcome.
-- Source attribution remains the standing repository constitution throughout.
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
-- Observer non-factorability: market income, Crown recognition and BIA's trust
-- asset category are all too coarse for richer target states.
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

biaTrustAssetCategoryCannotExhaustStewardshipValue :
  INF.FactorsThrough
    CarbonProjection.trustAssetObserver
    CarbonProjection.stewardshipValueOutcome → ⊥
biaTrustAssetCategoryCannotExhaustStewardshipValue =
  CarbonProjection.trustAssetCategoryCannotFactorStewardshipValue

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

cpiAnalysisIsIndependentNotGovernmentAuthored :
  Source.authorityKind Source.cpi2024RuralCreditAuthority
  ≡ Source.independentPolicyResearch
cpiAnalysisIsIndependentNotGovernmentAuthored = refl

cpiOfficialInputsDoNotTransferAuthorship :
  Source.usesOfficialUnderlyingData Source.cpi2024RuralCreditAuthority ≡ true
cpiOfficialInputsDoNotTransferAuthorship = refl

ashDatabookIsAcademicSynthesis :
  Source.authorityKind Source.ashCenter2025DatabookAuthority
  ≡ Source.academicDescriptiveStatisticalSynthesis
ashDatabookIsAcademicSynthesis = refl

biaCarbonClassificationIsAdministrativePolicy :
  Source.authorityKind Source.biaCarbon2023Authority
  ≡ Source.officialAdministrativePolicy
biaCarbonClassificationIsAdministrativePolicy = refl

abatablePriceIsCommercialObservation :
  Source.authorityKind Source.abatable2025ReddPriceAuthority
  ≡ Source.commercialMarketObservation
abatablePriceIsCommercialObservation = refl

------------------------------------------------------------------------
-- Additive evidence-design corrections.
------------------------------------------------------------------------

probstPreferredDesignIsFixedEffectsCausalChain :
  DesignCorrection.preferredDesign DesignCorrection.probst2020DesignCorrection
  ≡ DesignCorrection.fixedEffectsCausalChainDesign
probstPreferredDesignIsFixedEffectsCausalChain = refl

denBraberPreferredClaimVerbRemainsComparative :
  DesignCorrection.preferredClaimVerb DesignCorrection.denBraber2024ClaimVerbCorrection
  ≡ DesignCorrection.sourceReportsComparativeAssociationOrEstimatedDifference
denBraberPreferredClaimVerbRemainsComparative = refl

------------------------------------------------------------------------
-- Carbon valuation/market-price comparability.
------------------------------------------------------------------------

wriMitigationValueUsesPerHectareYear :
  CarbonValue.unit CarbonValue.wriBrazilCarbonMitigationValue
  ≡ CarbonValue.usdPerHectarePerYear
wriMitigationValueUsesPerHectareYear = refl

abatablePriceUsesPerTonneUnit :
  CarbonValue.unit CarbonValue.abatableBrazilReddMedianQ1_2025
  ≡ CarbonValue.usdPerTonneCO2e
abatablePriceUsesPerTonneUnit = refl

wriVsMarketPriceNeedsConversionReceipt :
  CarbonValue.comparability CarbonValue.wriMarketGapBoundary
  ≡ CarbonValue.conversionReceiptRequired
wriVsMarketPriceNeedsConversionReceipt = refl

exactUndercompensationRatioNotYetClaimed :
  CarbonValue.exactDirectUndercompensationRatioClaimed CarbonValue.wriMarketGapBoundary ≡ false
exactUndercompensationRatioNotYetClaimed = refl

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
-- Audit state: attribution rules pre-existed this tranche; the audit records
-- confirmed boundaries and local classification corrections.
------------------------------------------------------------------------

cpiAuditRecordsLocalCorrection :
  Audit.disposition Audit.cpiAuthorshipCorrection ≡ Audit.localClassificationCorrected
cpiAuditRecordsLocalCorrection = refl

ashAuditRecordsLocalCorrection :
  Audit.disposition Audit.ashAuthorshipCorrection ≡ Audit.localClassificationCorrected
ashAuditRecordsLocalCorrection = refl

dawsonAuditKeepsInterpretiveBridgeExplicit :
  Audit.disposition Audit.dawsonHingeAudit ≡ Audit.interpretiveBridgeRemainsExplicit
dawsonAuditKeepsInterpretiveBridgeExplicit = refl

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
  INF.FactorsThrough Income.cashIncomeObserver Income.landAuthorityOutcome → ⊥
cashIncomeCannotFactorLandAuthority = Income.cashIncomeDoesNotFactorLandAuthority

crownRecognitionCannotFactorIndigenousAuthority :
  INF.FactorsThrough Recognition.crownRecognitionObserver Recognition.indigenousAuthorityOutcome → ⊥
crownRecognitionCannotFactorIndigenousAuthority = Recognition.crownRecognitionDoesNotFactorIndigenousAuthority

workingPaperDoesNotBecomePeerReviewedClosure :
  Source.WorkingPaperEqualsPeerReviewedResult → ⊥
workingPaperDoesNotBecomePeerReviewedClosure = Source.workingPaperDoesNotEqualPeerReview

officialInputDoesNotTransferDerivedAuthorship :
  Source.OfficialUnderlyingDataMakesDerivedAnalysisOfficial → ⊥
officialInputDoesNotTransferDerivedAuthorship = Source.officialInputDoesNotTransferAuthorship

marketPriceDoesNotEqualSocialValue :
  Source.CommercialMarketPriceEqualsSocialValue → ⊥
marketPriceDoesNotEqualSocialValue = Source.marketPriceDoesNotEqualSocialValue

agencyCategoryDoesNotExhaustStewardshipValue :
  Source.AgencyPolicyClassificationExhaustsStewardshipValue → ⊥
agencyCategoryDoesNotExhaustStewardshipValue = Source.agencyCategoryDoesNotExhaustStewardshipValue

subsidyAssociationDoesNotCloseIncomeMechanism :
  Moderator.SubsidyExposureExplainsDenBraberIncomeCoefficient → ⊥
subsidyAssociationDoesNotCloseIncomeMechanism = Moderator.subsidiesDoNotDirectlyExplainCoefficientYet

crossStudyDifferenceDoesNotProveGovernanceModerator :
  Moderator.GovernanceModeratorProvedByCrossStudyDifferenceAlone → ⊥
crossStudyDifferenceDoesNotProveGovernanceModerator = Moderator.crossStudyDifferenceDoesNotProveModerator
