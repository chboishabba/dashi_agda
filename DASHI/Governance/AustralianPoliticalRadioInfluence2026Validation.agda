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

bannonPalmerIsDisputedSourceClaim :
  A.evidence A.palmerBannonConflict ≡ A.disputedDocumentClaim
bannonPalmerIsDisputedSourceClaim = refl

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

noPalmerHistoricalAutopromotion :
  A.ClaimAbout2019AdsProvesBannonDeployment → ⊥
noPalmerHistoricalAutopromotion = A.noPalmerClaimPromotion
