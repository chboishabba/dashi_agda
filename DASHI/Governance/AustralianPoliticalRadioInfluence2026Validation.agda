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
  A.kind A.aiimsProduction ≡ A.editorialPublication
aiimsIsProductionNotEquity = refl

nineStrategicPartnerNotOwner :
  A.kind A.nineTaptStrategicPartnership ≡ A.financialEntitlement
nineStrategicPartnerNotOwner = refl
