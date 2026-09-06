module DASHI.Cognition.PNF.SensibLawMaboTwoOrderLandBackEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackGlobalEvidenceExact as LandBack
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSocioeconomicModeratorHyperfabricExact as Moderator
import DASHI.Cognition.PNF.SensibLawMaboCriticalTheoryMaterialJusticeExact as Material
import DASHI.Cognition.PNF.SensibLawMaboColonialSovereigntyCriticalResidualExact as Critical

------------------------------------------------------------------------
-- Capstone: two legal orders + material LAND BACK evidence + source authority.
------------------------------------------------------------------------

crownOrderDoesNotDetermineIndigenousOrderExistence :
  TwoOrder.courtDeterminesOrderExistence TwoOrder.indigenousOrderFibre ≡ false
crownOrderDoesNotDetermineIndigenousOrderExistence = refl

crownRecognitionDoesNotCreateIndigenousOrder :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
crownRecognitionDoesNotCreateIndigenousOrder = refl

nativeTitleInterfaceDoesNotDeclareCrownGlobalSupremacy :
  TwoOrder.crownOrderGloballySupreme TwoOrder.nativeTitleRecognitionInterface ≡ false
nativeTitleInterfaceDoesNotDeclareCrownGlobalSupremacy = refl

nativeTitleInterfaceDoesNotReduceIndigenousLawToFacts :
  TwoOrder.indigenousOrderReducedToFactInput TwoOrder.nativeTitleRecognitionInterface ≡ false
nativeTitleInterfaceDoesNotReduceIndigenousLawToFacts = refl

sovereigntyExternalisationDoesNotSettleIndigenousOrder :
  TwoOrder.crownOrderGloballySupreme TwoOrder.sovereigntyExternalisationInterface ≡ false
sovereigntyExternalisationDoesNotSettleIndigenousOrder = refl

------------------------------------------------------------------------
-- Dawson hinge remains the first court-internal mediation question.
------------------------------------------------------------------------

dawsonRadicalTitleRecognitionBridgeRemainsContested :
  TwoOrder.status TwoOrder.radicalTitleToRecognitionCondition ≡ TwoOrder.contestedCourtInternalBridge
dawsonRadicalTitleRecognitionBridgeRemainsContested = refl

dawsonBridgeDoesNotProveColonialLegitimacy :
  TwoOrder.provesColonialLegitimacy TwoOrder.radicalTitleToRecognitionCondition ≡ false
dawsonBridgeDoesNotProveColonialLegitimacy = refl

------------------------------------------------------------------------
-- LAND BACK evidence is domain-relative but already strong on important axes.
------------------------------------------------------------------------

deforestationEvidenceIsStrongCausal :
  LandBack.deforestationState LandBack.currentGlobalEvidenceState ≡ LandBack.strongCausalSupportMapped
deforestationEvidenceIsStrongCausal = refl

restorationEvidenceIsStrongCausal :
  LandBack.restorationState LandBack.currentGlobalEvidenceState ≡ LandBack.strongCausalSupportMapped
restorationEvidenceIsStrongCausal = refl

mentalHealthDispossessionEvidenceIsSystematic :
  LandBack.mentalHealthState LandBack.currentGlobalEvidenceState ≡ LandBack.systematicHarmEvidenceMapped
mentalHealthDispossessionEvidenceIsSystematic = refl

privateTitlingProxyRemainsInvalid :
  LandBack.privateTitlingProxyState LandBack.currentGlobalEvidenceState ≡ LandBack.mixedTradeoffMapped
privateTitlingProxyRemainsInvalid = refl

landBackHypothesisHasStrongEnvironmentalSupport :
  LandBack.environmentalSupportStrong LandBack.landBackGlobalEvidenceHypothesis ≡ true
landBackHypothesisHasStrongEnvironmentalSupport = refl

landBackHypothesisHasStrongDispossessionHarmSupport :
  LandBack.dispossessionHarmSupportStrong LandBack.landBackGlobalEvidenceHypothesis ≡ true
landBackHypothesisHasStrongDispossessionHarmSupport = refl

landBackDoesNotYetProveEverySocioeconomicOutcome :
  LandBack.everySocioeconomicOutcomeProved LandBack.landBackGlobalEvidenceHypothesis ≡ false
landBackDoesNotYetProveEverySocioeconomicOutcome = refl

------------------------------------------------------------------------
-- Refined socioeconomic interpretation supersedes the coarse scalar for
-- downstream analysis without deleting the historical coarse atlas receipt.
------------------------------------------------------------------------

socioeconomicAggregateLabelIsTooCoarse :
  Moderator.aggregateLabel Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.aggregateTradeoffLabelTooCoarse
socioeconomicAggregateLabelIsTooCoarse = refl

incomeSignalIsComparatorSpecific :
  Moderator.incomeState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.incomePenaltyComparatorSpecific
incomeSignalIsComparatorSpecific = refl

inequalitySignalIncludesPositiveIndigenousTerritoryResults :
  Moderator.inequalityState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.inequalityBenefitComparatorSpecific
inequalitySignalIncludesPositiveIndigenousTerritoryResults = refl

literacySanitationDoNotShowUniformPenalty :
  Moderator.serviceIndicatorState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.literacySanitationNoUniformPenalty
literacySanitationDoNotShowUniformPenalty = refl

usLandBackEconomicSignalRemainsWorkingPaperGrade :
  Moderator.usEconomicState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.usWorkingPaperPositiveEconomicSignal
usLandBackEconomicSignalRemainsWorkingPaperGrade = refl

governanceModeratorIdentificationRemainsOpen :
  Moderator.moderatorState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.governanceModeratorIdentificationOpen
governanceModeratorIdentificationRemainsOpen = refl

------------------------------------------------------------------------
-- Source-authority firewalls.
------------------------------------------------------------------------

usLandBackStudyIsWorkingPaperNotPeerReviewed :
  Source.publicationStatus Source.arcoiteJohnson2025Authority ≡ Source.workingPaperNotPeerReviewed
usLandBackStudyIsWorkingPaperNotPeerReviewed = refl

doiBuyBackTotalsAreAdministrativeReceipts :
  Source.authorityKind Source.doiLandBuyBackAuthority ≡ Source.officialAdministrativeReceipt
doiBuyBackTotalsAreAdministrativeReceipts = refl

wriBenefitNumbersAreValuationNotCausalTrial :
  Source.authorityKind Source.wriTenureEconomicValuationAuthority ≡ Source.economicValuationReport
wriBenefitNumbersAreValuationNotCausalTrial = refl

cpiCreditReceiptDoesNotDirectlyIdentifyIncomeMechanism :
  Moderator.directCausalContributionToIncomeDifferenceProved Moderator.cpiCreditDistortionReceipt ≡ false
cpiCreditReceiptDoesNotDirectlyIdentifyIncomeMechanism = refl

historicalSubsidyReceiptDoesNotAutoGeneraliseToPresent :
  Moderator.directCausalContributionToIncomeDifferenceProved Moderator.binswangerHistoricalDistortionReceipt ≡ false
historicalSubsidyReceiptDoesNotAutoGeneraliseToPresent = refl

------------------------------------------------------------------------
-- Opportunity-cost/externality context.
------------------------------------------------------------------------

wriSoyOpportunityCostContext :
  Moderator.soyAnnualUsdPerHa Moderator.wriOpportunityCostContext ≡ 450
wriSoyOpportunityCostContext = refl

wriPastureOpportunityCostContext :
  Moderator.pastureAnnualUsdPerHa Moderator.wriOpportunityCostContext ≡ 78
wriPastureOpportunityCostContext = refl

wriTimberOpportunityCostContext :
  Moderator.timberAnnualUsdPerHa Moderator.wriOpportunityCostContext ≡ 25
wriTimberOpportunityCostContext = refl

conversionOpportunityCostIsNotSocialWelfare :
  Moderator.conversionValueEqualsSocialWelfare Moderator.wriOpportunityCostContext ≡ false
conversionOpportunityCostIsNotSocialWelfare = refl

indigenousOpportunityCostLogicNotDirectlyApplicable :
  Moderator.indigenousOpportunityCostLogicDirectlyApplicable Moderator.wriOpportunityCostContext ≡ false
indigenousOpportunityCostLogicNotDirectlyApplicable = refl

------------------------------------------------------------------------
-- Component x governance-condition -> outcome hyperfabric examples.
------------------------------------------------------------------------

collectiveTenureDeforestationIsPeerReviewedCausal :
  Moderator.status Moderator.collectiveTenureDeforestationEdge ≡ Moderator.peerReviewedCausalMapped
collectiveTenureDeforestationIsPeerReviewedCausal = refl

collectiveTenureRestorationIsPeerReviewedCausal :
  Moderator.status Moderator.collectiveTenureRestorationEdge ≡ Moderator.peerReviewedCausalMapped
collectiveTenureRestorationIsPeerReviewedCausal = refl

usLandBackIncomeEdgeRemainsWorkingPaperCausalClaim :
  Moderator.status Moderator.landBackUsIncomeEdge ≡ Moderator.workingPaperCausalClaimMapped
usLandBackIncomeEdgeRemainsWorkingPaperCausalClaim = refl

extractivePressureIncomeMechanismRemainsOpen :
  Moderator.status Moderator.extractivePressureIncomeInterpretationEdge ≡ Moderator.moderatorHypothesisOpen
extractivePressureIncomeMechanismRemainsOpen = refl

------------------------------------------------------------------------
-- Material repair cannot be paid by source recognition alone.
------------------------------------------------------------------------

nativeTitleRecognitionCurrentlySourceMapped :
  Material.nativeTitleRecognition Material.currentCriticalRepairState ≡ Material.repairAxisSourceMapped
nativeTitleRecognitionCurrentlySourceMapped = refl

landReturnStillOpen :
  Material.landReturn Material.currentCriticalRepairState ≡ Material.repairAxisOpen
landReturnStillOpen = refl

sovereigntyRecognitionStillOpen :
  Material.sovereigntyRecognition Material.currentCriticalRepairState ≡ Material.repairAxisOpen
sovereigntyRecognitionStillOpen = refl

materialReparationStillOpen :
  Material.materialReparation Material.currentCriticalRepairState ≡ Material.repairAxisOpen
materialReparationStillOpen = refl

------------------------------------------------------------------------
-- Strong material regression: recognition of significance != protection.
------------------------------------------------------------------------

barrambinSignificanceAcknowledged :
  Material.significanceAcknowledged Material.barrambin2026Receipt ≡ true
barrambinSignificanceAcknowledged = refl

barrambinProtectionNotGranted :
  Material.emergencyProtectionGranted Material.barrambin2026Receipt ≡ false
barrambinProtectionNotGranted = refl

------------------------------------------------------------------------
-- Critical sovereignty state remains outside Crown doctrinal closure.
------------------------------------------------------------------------

nativeTitleDoesNotCloseSovereignty :
  Critical.NativeTitleRecognitionProvesSovereigntyRecognition → ⊥
nativeTitleDoesNotCloseSovereignty = Critical.nativeTitleDoesNotProveSovereigntyRecognition

nativeTitleDoesNotRepairDispossession :
  Critical.NativeTitleRecognitionRepairsDispossession → ⊥
nativeTitleDoesNotRepairDispossession = Critical.nativeTitleDoesNotRepairDispossessionByItself

------------------------------------------------------------------------
-- No-collapse laws exposed at the capstone surface.
------------------------------------------------------------------------

genericPrivateTitleIsNotLandBack : LandBack.GenericPrivateTitleEqualsLandBack → ⊥
genericPrivateTitleIsNotLandBack = LandBack.genericTitleDoesNotEqualLandBack

legalTitleAloneIsNotIndigenousAuthority : LandBack.LegalTitleAloneEqualsIndigenousAuthority → ⊥
legalTitleAloneIsNotIndigenousAuthority = LandBack.legalTitleAloneDoesNotEqualAuthority

forestSuccessDoesNotProveAllSocialOutcomes : LandBack.ForestEvidenceProvesEverySocialOutcome → ⊥
forestSuccessDoesNotProveAllSocialOutcomes = LandBack.forestEvidenceDoesNotProveEverySocialOutcome

workingPaperDoesNotBecomePeerReview : Source.WorkingPaperEqualsPeerReviewedResult → ⊥
workingPaperDoesNotBecomePeerReview = Source.workingPaperDoesNotEqualPeerReview

valuationDoesNotBecomeCausalEffect : Source.EconomicValuationEqualsCausalEffect → ⊥
valuationDoesNotBecomeCausalEffect = Source.valuationDoesNotEqualCausalEffect

subsidyExposureDoesNotYetExplainAmazonIncomeCoefficient :
  Moderator.SubsidyExposureExplainsDenBraberIncomeCoefficient → ⊥
subsidyExposureDoesNotYetExplainAmazonIncomeCoefficient = Moderator.subsidiesDoNotDirectlyExplainCoefficientYet

lowerMarketIncomeDoesNotAutomaticallyMeanLowerWelfare :
  Moderator.LowerMarketIncomeEqualsLowerCommunityWelfare → ⊥
lowerMarketIncomeDoesNotAutomaticallyMeanLowerWelfare = Moderator.lowerMarketIncomeDoesNotAutomaticallyMeanLowerWelfare

crossStudyDifferenceDoesNotByItselfProveGovernanceModerator :
  Moderator.GovernanceModeratorProvedByCrossStudyDifferenceAlone → ⊥
crossStudyDifferenceDoesNotByItselfProveGovernanceModerator = Moderator.crossStudyDifferenceDoesNotProveModerator

crownOrderDoesNotContainIndigenousOrder : TwoOrder.CrownOrderContainsIndigenousOrder → ⊥
crownOrderDoesNotContainIndigenousOrder = TwoOrder.aCrownOrderDoesNotContainIndigenousOrder

municipalEffectDoesNotProveLegitimateSovereigntyTransfer :
  TwoOrder.MunicipalLegalEffectProvesLegitimateSovereigntyTransfer → ⊥
municipalEffectDoesNotProveLegitimateSovereigntyTransfer = TwoOrder.municipalEffectDoesNotProveLegitimateTransfer
