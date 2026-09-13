module DASHI.Law.AustraliaIsraelInfluenceLobbyingSpeechGovernanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Australia/Israel influence, lobbying and speech-governance source receipts.
--
-- This owner keeps three different things apart:
--   1. overt public-affairs / sponsored-access activity in Australia;
--   2. documented or reported covert influence operations elsewhere; and
--   3. parliamentary control of Israel/Palestine political speech in Australia.
--
-- None of these, alone or together, prove that a particular Australian foreign
-- policy decision was covertly directed or donor-controlled.
------------------------------------------------------------------------

data InfluenceMode : Set where
  overtPublicAffairs : InfluenceMode
  sponsoredTravelAccess : InfluenceMode
  covertInfluenceOperation : InfluenceMode
  parliamentarySpeechControl : InfluenceMode
  unresolvedRecentWithdrawalClaim : InfluenceMode

data SourceStatus : Set where
  primarySelfDescription : SourceStatus
  officialParliamentarySource : SourceStatus
  multiSourceReported : SourceStatus
  searchResidual : SourceStatus

record InfluenceReceipt : Set where
  constructor influenceReceipt
  field
    mode : InfluenceMode
    status : SourceStatus
    sourceReference : String
    boundedDescription : String
    australianDecisionCausation : Bool

open InfluenceReceipt public

aijacPublicAffairsReceipt : InfluenceReceipt
aijacPublicAffairsReceipt = influenceReceipt overtPublicAffairs primarySelfDescription
  "AIJAC, About AIJAC, checked 2026-09-09"
  "AIJAC describes itself as a public-affairs organisation conveying Australian Jewish community interests to government, media and other organisations."
  false

aijacRambamReceipt : InfluenceReceipt
aijacRambamReceipt = influenceReceipt sponsoredTravelAccess primarySelfDescription
  "AIJAC, About AIJAC, checked 2026-09-09"
  "AIJAC states that its Rambam Israel Fellowship annually sponsors visits to Israel by selected senior journalists, politicians, political advisers, senior public servants and student leaders."
  false

stoicInfluenceReceipt : InfluenceReceipt
stoicInfluenceReceipt = influenceReceipt covertInfluenceOperation multiSourceReported
  "2024 reporting on Meta/OpenAI disruption of STOIC-linked coordinated inauthentic behaviour; reporting attributed Israeli Ministry of Diaspora Affairs sponsorship while the ministry denied involvement"
  "A covert pro-Israel influence campaign using fake personas and synthetic/AI-assisted content was publicly disrupted; government sponsorship was reported by multiple sources but denied by the ministry. This establishes a relevant capability/history coordinate, not Australian-target causation."
  false

berkmanPoliticalExpressionReceipt : InfluenceReceipt
berkmanPoliticalExpressionReceipt = influenceReceipt parliamentarySpeechControl officialParliamentarySource
  "Queensland Parliament, Michael Berkman speech 3 March 2026 and e-petition 4656-26 sponsored 11 August 2026"
  "Berkman publicly contested laws and parliamentary/political classifications that he said conflate criticism of Israel/Zionism with antisemitism; in August 2026 he sponsored a petition seeking repeal of political-expression provisions used against Palestine-solidarity protest."
  false

berkmanRecentTakeBackResidual : InfluenceReceipt
berkmanRecentTakeBackResidual = influenceReceipt unresolvedRecentWithdrawalClaim searchResidual
  "web search 2026-09-09; exact recent Hansard sitting/withdrawal sequence not recovered"
  "The remembered claim that Berkman was required to take back Israel/Palestine-related statements several times in one recent day remains a source-location residual; do not promote count, wording or date until the exact Hansard/record is recovered."
  false

record InfluenceBoundary : Set where
  constructor influenceBoundary
  field
    overtLobbyingEqualsCovertOperation : Bool
    overtLobbyingEqualsCovertOperationIsFalse : overtLobbyingEqualsCovertOperation ≡ false
    sponsoredTravelProvesPolicyControl : Bool
    sponsoredTravelProvesPolicyControlIsFalse : sponsoredTravelProvesPolicyControl ≡ false
    foreignInfluenceCapabilityProvesAustralianTargeting : Bool
    foreignInfluenceCapabilityProvesAustralianTargetingIsFalse : foreignInfluenceCapabilityProvesAustralianTargeting ≡ false
    speechRestrictionProvesForeignDirection : Bool
    speechRestrictionProvesForeignDirectionIsFalse : speechRestrictionProvesForeignDirection ≡ false
    combinedCoordinatesJustifyInfluenceInquiry : Bool
    combinedCoordinatesJustifyInfluenceInquiryIsTrue : combinedCoordinatesJustifyInfluenceInquiry ≡ true

canonicalInfluenceBoundary : InfluenceBoundary
canonicalInfluenceBoundary = influenceBoundary false refl false refl false refl false refl true refl
