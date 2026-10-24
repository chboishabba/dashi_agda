module DASHI.Governance.AustralianPoliticalRadioInfluence2026Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.AustralianPoliticalRadioInfluence2026Exact as A

-- A first-person account is represented as an account, not magically promoted
-- to a signed contract, a named audience impact or a party instruction.
kyleMessagingIsActorAccount :
  A.evidence A.kyleHansonMessaging ≡ A.namedActorSelfReport
kyleMessagingIsActorAccount = refl

oneNationDenialIsSeparatelyAttributable :
  A.evidence A.ashbyKyleQualification ≡ A.namedActorDenial
oneNationDenialIsSeparatelyAttributable = refl

acmaMpoxIsRegulatoryFinding :
  A.evidence A.acmaMpoxFinding ≡ A.regulatoryDetermination
acmaMpoxIsRegulatoryFinding = refl

arnFinancialInterestIsNotPoliticalTransfer :
  A.kind A.arnSandilandsRevenue ≡ A.financialEntitlement
arnFinancialInterestIsNotPoliticalTransfer = refl

noAutomaticEditorialControl :
  A.provesEditorialControl A.arnSandilandsRevenue ≡ false
noAutomaticEditorialControl = refl

noAutoBannonCoordination :
  A.provesHiddenCoordination A.advanceBannonAssociate ≡ false
noAutoBannonCoordination = refl

noUniversalPolicyCapture :
  A.provesPolicyCausation A.rinehartHansonPolicy ≡ false
noUniversalPolicyCapture = refl

noFundCommand : A.FundingImpliesEditorialControl → ⊥
noFundCommand = A.noFundToEditorialLeap

noConferenceCommand : A.SharedConferenceImpliesBannonCommand → ⊥
noConferenceCommand = A.noCoattendanceCommandLeap

noPaidCampaignPromotion : A.MessagingSelfReportImpliesPaidContract → ⊥
noPaidCampaignPromotion = A.noEmploymentLeap

noFordhamDirection : A.SimilarClimateFramingImpliesFordhamDirection → ⊥
noFordhamDirection = A.noFordhamCommandLeap

noNewRadioRevenueDirection : A.MediaRevenueShareImpliesEditorialOrders → ⊥
noNewRadioRevenueDirection = A.noRevenueControlLeap


-- Legal operator is a registry entry; whether it proves all shareholders
-- is a separate private-share-register inquiry.
legalOperatorIsRegistrySource :
  A.evidence A.newShowLegalOperator ≡ A.institutionRecord
legalOperatorIsRegistrySource = refl

newShowInterestIsFirstPersonNotEquityEvidence :
  A.evidence A.sandilandsSelfReportedOwnership ≡ A.namedActorSelfReport
newShowInterestIsFirstPersonNotEquityEvidence = refl

arnIsNetRevenueCounterparty :
  A.kind A.arnSandilandsRevenue ≡ A.financialEntitlement
arnIsNetRevenueCounterparty = refl

aiimsIsProductionNotEquity :
  A.kind A.aiimsProduction ≡ A.productionSupply
aiimsIsProductionNotEquity = refl

nineStrategicPartnerNotOwner :
  A.kind A.nineTaptStrategicPartnership ≡ A.announcedStrategicPartnership
nineStrategicPartnerNotOwner = refl

quasarShareHoldingAsDated :
  A.kind A.quasarARNHistoricalEquity ≡ A.historicEquityHolding
quasarShareHoldingAsDated = refl

quasarServiceIsNotNewShowEquity :
  A.kind A.quasarKyleService ≡ A.productionSupply
quasarServiceIsNotNewShowEquity = refl

hendersonShareHoldingAsDated :
  A.kind A.hendersonARNHistoricalEquity ≡ A.historicEquityHolding
hendersonShareHoldingAsDated = refl

southernCrossARNEquityAsDated :
  A.kind A.southernCrossARNIndirect ≡ A.historicEquityHolding
southernCrossARNEquityAsDated = refl

stokesSouthernCrossEquityAsDated :
  A.kind A.stokesSouthernCrossStake ≡ A.historicEquityHolding
stokesSouthernCrossEquityAsDated = refl

newShowOperatorIsNotOwnership :
  A.kind A.newShowLegalOperator ≡ A.legalOperatorRegistration
newShowOperatorIsNotOwnership = refl

proposedBuyoutIsNotCompleted :
  A.kind A.kyleProposedARNBuyout ≡ A.proposedUncompletedAcquisition
proposedBuyoutIsNotCompleted = refl

subscriberFundingIsAttributedOnly :
  A.evidence A.kyleSubscriberFinanceSelfReport ≡ A.namedActorSelfReport
subscriberFundingIsAttributedOnly = refl

harveyNormanOfferIsNotRealisedCash :
  A.kind A.harveyNormanProspectiveSponsorship ≡ A.prospectiveSponsorOffer
harveyNormanOfferIsNotRealisedCash = refl

uscreenPlatformIsNotEquity :
  A.kind A.kyleUscreenPlatform ≡ A.externalPlatformSupplier
uscreenPlatformIsNotEquity = refl

reportedCustomersAreNotAuditedBankBalance :
  A.SubscriptionSelfReportEstablishesAuditedReceipts → ⊥
reportedCustomersAreNotAuditedBankBalance = A.reportedSubscriptionsNotAudited

advertiserInterestNotCapitalStake :
  A.BrandOfferEstablishesEquityInvestment → ⊥
advertiserInterestNotCapitalStake = A.advertiserOfferNotEquity


-- Consolidated media source-join regressions. Evidence grades are source-local;
-- these reduction witnesses cannot independently verify historical accounts.
rinehartStakeIsSecuredFinancing :
  A.kind A.rinehartMcWilliamSecuredMediaStake ≡ A.securedStakeFinancing
rinehartStakeIsSecuredFinancing = refl

stefanovicFundingRemainsReported :
  A.kind A.rinehartStefanovicPodcastFundingClaim ≡ A.reportedUnverifiedFunding
stefanovicFundingRemainsReported = refl

hansonRepostIsRedistribution :
  A.kind A.hansonRepublishedRobinson ≡ A.mediaRedistribution
hansonRepostIsRedistribution = refl

sheahanChatRemainsReported :
  A.kind A.advanceSheahanBannonConversation ≡ A.reportedMeeting
sheahanChatRemainsReported = refl

taxEvidenceIsCorrespondence :
  A.kind A.mandelsonXstrataEpsteinTaxEmail ≡ A.publishedCorrespondence
taxEvidenceIsCorrespondence = refl

sharedLaunchDoesNotProveControl :
  A.provesHiddenCoordination A.rinehartBannonDevineEvent ≡ false
sharedLaunchDoesNotProveControl = refl

stakeLoanDoesNotProveEditorialOrders :
  A.provesEditorialControl A.rinehartMcWilliamSecuredMediaStake ≡ false
stakeLoanDoesNotProveEditorialOrders = refl

headquartersIsReportedLease :
  A.kind A.rinehartOneNationHeadOffice ≡ A.commercialLeaseArrangement
headquartersIsReportedLease = refl

podcastBuyoutNotRinehartEquity :
  A.kind A.stefanovicIbrahimOwnershipSettlement ≡ A.ownershipBuyoutSettlement
podcastBuyoutNotRinehartEquity = refl

MFWPressureIsAdvertiserCampaign :
  A.kind A.mfwKyleAdvertiserCampaign ≡ A.advertiserBoycottCampaign
MFWPressureIsAdvertiserCampaign = refl

noMeetingFromIndexReference :
  A.EpsteinDocumentMentionProvesMeeting → ⊥
noMeetingFromIndexReference = A.noMentionMeeting

noReportedFundingToEquityLeap :
  A.ReportedPodcastBackerIsAuditedCapital → ⊥
noReportedFundingToEquityLeap = A.noRumourToEquity

noInstructionsFromInterviewCopy :
  A.OriginalInterviewFileAccessIsProvenInstruction → ⊥
noInstructionsFromInterviewCopy = A.noRepublishedFileCommand


-- Case-bounded source-originality witnesses. Equality reductions check
-- the explicit classifications only, not the independent historical facts.
reefReleaseIsTimedMediaAccess :
  A.kind A.leyAimsTargetedMediaPreview ≡ A.timedTargetedInformationRelease
reefReleaseIsTimedMediaAccess = refl

riddOpinionNotAimsMeasurement :
  A.kind A.riddIndependentReefOpinion ≡ A.originalOpinionProduction
riddOpinionNotAimsMeasurement = refl

mooreRepostNotIndependentMeasurement :
  A.kind A.mooreAmplifiedRiddReefClaim ≡ A.traceableClaimAmplification
mooreRepostNotIndependentMeasurement = refl

reefRegulatoryFindingIsSpecific :
  A.evidence A.acmaReefOutsidersFinding ≡ A.regulatoryDetermination
reefRegulatoryFindingIsSpecific = refl

reefReleaseNotMinistryEditorialControl :
  A.provesEditorialControl A.leyAimsTargetedMediaPreview ≡ false
reefReleaseNotMinistryEditorialControl = refl

riddDistributionNotCoordinatedCommand :
  A.provesHiddenCoordination A.mooreAmplifiedRiddReefClaim ≡ false
riddDistributionNotCoordinatedCommand = refl


outsidersLloydRiddSameProgrammeIsPublished :
  A.kind A.skyOutsidersLloydRiddSameProgramme ≡ A.editorialPublication
outsidersLloydRiddSameProgrammeIsPublished = refl

ipaOwnTranscriptIsDerivativePublication :
  A.kind A.ipaHostsBOMOutsidersTranscript ≡ A.traceableClaimAmplification
ipaOwnTranscriptIsDerivativePublication = refl

riddFellowshipIsNamedInstitutionalRelation :
  A.kind A.ipaRiddResearchFellowship ≡ A.professionalAffiliation
riddFellowshipIsNamedInstitutionalRelation = refl

historicHancockIPAIsNotCurrentEarmarkedPayment :
  A.kind A.hancockToIPAHistoricalFunding ≡ A.historicalInstitutionalFunding
historicHancockIPAIsNotCurrentEarmarkedPayment = refl

historicalIPAReceiptNotEditorialOrder :
  A.provesEditorialControl A.hancockToIPAHistoricalFunding ≡ false
historicalIPAReceiptNotEditorialOrder = refl

publishedBOMInterviewNotSecretCommand :
  A.provesHiddenCoordination A.skyOutsidersLloydRiddSameProgramme ≡ false
publishedBOMInterviewNotSecretCommand = refl


creightonOriginalCreditIsAttributedReuse :
  A.kind A.creightonIPAOriginalArticle ≡ A.traceableClaimAmplification
creightonOriginalCreditIsAttributedReuse = refl

gasProducerLinksIPAOriginal :
  A.kind A.senexLinksIPACreighton ≡ A.traceableClaimAmplification
gasProducerLinksIPAOriginal = refl

hancockSameJournalismNotIndependentData :
  A.kind A.hancockReprintsJohnsonNightly ≡ A.traceableClaimAmplification
hancockSameJournalismNotIndependentData = refl

senexSameJournalismNotIndependentData :
  A.kind A.senexLinksJohnsonNightly ≡ A.traceableClaimAmplification
senexSameJournalismNotIndependentData = refl

parliamentaryPublicPolicyCounterexample :
  A.kind A.senateGasTaxInquiryPublicComparator ≡ A.editorialPublication
parliamentaryPublicPolicyCounterexample = refl

gasRepublishingDoesNotEstablishPolicyCopy :
  A.LinkedIndustryArticleProvesPartyDrafting → ⊥
gasRepublishingDoesNotEstablishPolicyCopy = A.linkedIndustryArticleNotPartyDrafting

politicalLanguageDoesNotEstablishCommonSponsor :
  A.CommonPoliticalArgumentProvesSharedSponsor → ⊥
politicalLanguageDoesNotEstablishCommonSponsor = A.commonArgumentDoesNotProveSponsor
