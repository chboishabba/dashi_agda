module DASHI.Cognition.BannonFaragePalmerAutomatedInfluenceReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA
import DASHI.Cognition.NickLandProvocationOverreactionPopulistTransferExact as Land
import DASHI.Governance.HansonOneNationPoliticalEcologyExact as Hanson

------------------------------------------------------------------------
-- BANNON / FARAGE / PALMER / AUTOMATED POLITICAL INFLUENCE RECEIPTS
--
-- Claim-local receipts only.  Direct conversations, claimed influence,
-- campaign infrastructure, platform amplification and third-party engagement
-- farms remain distinct coordinates.
------------------------------------------------------------------------

data InfluenceObject : Set where
  farageBannonMovementPlanning : InfluenceObject
  palmerMassSMS : InfluenceObject
  palmerSaturationAdvertising : InfluenceObject
  bannonPalmerInfluenceClaim : InfluenceObject
  oneNationOfficialAIContent : InfluenceObject
  proOneNationForeignEngagementFarms : InfluenceObject
  bannonLandYarvinIntellectualLineage : InfluenceObject
  bannonExplicitLandCredit : InfluenceObject

record InfluenceReceipt : Set where
  constructor influence-receipt
  field
    object : InfluenceObject
    source : String
    boundedFinding : String
    directContactPaid : Bool
    deploymentPaid : Bool
    claimedInfluencePaid : Bool
    independentlyVerifiedInfluencePaid : Bool
    commonCommandPaid : Bool
open InfluenceReceipt public

farageBannonReceipt : InfluenceReceipt
farageBannonReceipt = influence-receipt
  farageBannonMovementPlanning
  "Guardian 2019 reporting based on Alison Klayman/The Brink footage of 2017-2018 meetings"
  "Farage and Bannon directly discussed a transnational populist alliance later called The Movement. Farage called the concept a fightback against globalists and discussed the proposed organisation as a clearing house for ideas, funding and polling/campaign help."
  true true true true false

palmerSMSReceipt : InfluenceReceipt
palmerSMSReceipt = influence-receipt
  palmerMassSMS
  "ABC News 2019; Parliamentary Joint Standing Committee on Electoral Matters record"
  "Palmer/UAP sent geographically targeted unsolicited political SMS and robocalls at national scale. Palmer said 5.6 million phones received campaign texts; parliamentary evidence records extensive complaints."
  false true false true false

palmerSaturationReceipt : InfluenceReceipt
palmerSaturationReceipt = influence-receipt
  palmerSaturationAdvertising
  "AEC/election reporting; ABC/Guardian 2019 and 2026 retrospectives"
  "Palmer deployed an unprecedented saturation advertising campaign across television, radio, print, digital and SMS, with anti-Labor, anti-China and anti-climate messaging. Exact causal effect on the 2019 result remains contested."
  false true false true false

bannonPalmerReceipt : InfluenceReceipt
bannonPalmerReceipt = influence-receipt
  bannonPalmerInfluenceClaim
  "US DOJ-released Epstein files EFTA01615861; ABC/Guardian 2026 reporting; Palmer public denial"
  "A message attributed to Steve Bannon states 'I had Clive Palmer do the $60 million anti china and climate change ads'. Palmer later acknowledged one brief phone conversation with Bannon but denied Bannon directed the campaign. The existence of Bannon's claim and a Bannon-Palmer call are paid; Bannon's claimed operational control is disputed and not independently verified."
  true true true false false

oneNationAIReceipt : InfluenceReceipt
oneNationAIReceipt = influence-receipt
  oneNationOfficialAIContent
  "ABC News Verify and 2026 Australian election reporting"
  "One Nation has deliberately deployed AI-generated campaign videos and online-first provocative political content through official party channels and associated production partners."
  false true false true false

foreignMemeFarmReceipt : InfluenceReceipt
foreignMemeFarmReceipt = influence-receipt
  proOneNationForeignEngagementFarms
  "Guardian Australia and ABC News Verify 2026 investigations"
  "Large pro-One Nation Facebook groups contain AI-generated and replicated outrage content produced by overseas engagement-farm or creator-economy accounts. Reporting found genuine Australian audiences but did not establish that the party commissioned or controlled those foreign operations."
  false true false true false

landYarvinBannonReceipt : InfluenceReceipt
landYarvinBannonReceipt = influence-receipt
  bannonLandYarvinIntellectualLineage
  "Politico 2017 Bannon reading/influence reporting; later academic literature on Dark Enlightenment/NRx; Financial Times 2025"
  "Bannon is documented as a reader/admirer of Curtis Yarvin/Moldbug, whose political neoreactionary programme is tightly coupled in the literature with Nick Land's Dark Enlightenment and right-accelerationist synthesis. This pays an intellectual-lineage route into Bannon-world stronger than mere structural resemblance."
  true false true true false

explicitLandCreditStatus : InfluenceReceipt
explicitLandCreditStatus = influence-receipt
  bannonExplicitLandCredit
  "Current web acquisition round through 2026-10-13"
  "Multiple secondary sources describe Land as influential on Bannon or as a guru within Bannon's ideological milieu, but this acquisition round did not locate a primary Bannon statement explicitly crediting Nick Land by name. That narrower receipt remains open."
  false false false false false

------------------------------------------------------------------------
-- Non-collapse boundaries.
------------------------------------------------------------------------

data ClaimedInfluenceImpliesVerifiedControl : Set where
data ForeignSupporterAmplificationImpliesPartyCommissioning : Set where
data MassMessagingImpliesDisinformation : Set where
data DirectContactImpliesCommonCommand : Set where
data IntellectualLineageImpliesOperationalDirection : Set where

claimedInfluenceDoesNotCreateVerifiedControl : ClaimedInfluenceImpliesVerifiedControl → ⊥
claimedInfluenceDoesNotCreateVerifiedControl ()

foreignAmplificationDoesNotCreateCommissioning : ForeignSupporterAmplificationImpliesPartyCommissioning → ⊥
foreignAmplificationDoesNotCreateCommissioning ()

massMessagingDoesNotByItselfCreateDisinformation : MassMessagingImpliesDisinformation → ⊥
massMessagingDoesNotByItselfCreateDisinformation ()

directContactDoesNotCreateCommonCommand : DirectContactImpliesCommonCommand → ⊥
directContactDoesNotCreateCommonCommand ()

intellectualLineageDoesNotCreateOperationalDirection : IntellectualLineageImpliesOperationalDirection → ⊥
intellectualLineageDoesNotCreateOperationalDirection ()

------------------------------------------------------------------------
-- Acquisition frontier.
------------------------------------------------------------------------

data InfluenceDebt : Set where
  locatePrimaryBannonLandCredit : InfluenceDebt
  resolveBannonPalmerCallChronology : InfluenceDebt
  resolvePalmerCampaignVendorStack : InfluenceDebt
  resolveOneNationOfficialAutomationStack : InfluenceDebt
  resolveForeignMemeFarmPartyCommissioning : InfluenceDebt
  resolveFarageBannonTechniqueTransfer : InfluenceDebt

record InfluenceAcquisition : Set where
  constructor influence-acquisition
  field
    debt : InfluenceDebt
    priority : Nat
    question : String
open InfluenceAcquisition public

canonicalInfluenceAcquisition : List InfluenceAcquisition
canonicalInfluenceAcquisition =
  influence-acquisition resolveBannonPalmerCallChronology 100
    "Reconstruct the Bannon-Palmer contact timeline, including phone records, intermediaries, advisers and whether the call preceded or followed the anti-China/anti-climate creative strategy."
  ∷ influence-acquisition resolvePalmerCampaignVendorStack 99
    "Identify the agencies, SMS vendors, data brokers, targeting systems, media-buying firms and analytics stack behind the 2019 Palmer/UAP saturation campaign."
  ∷ influence-acquisition resolveFarageBannonTechniqueTransfer 98
    "Resolve which Bannon/Movement polling, analytics, social-media, candidate-selection or fundraising methods actually transferred into Farage/Brexit Party/Reform operations."
  ∷ influence-acquisition resolveOneNationOfficialAutomationStack 97
    "Identify One Nation's official AI generation, scheduling, targeting, ad-tech, CRM, social-distribution and analytics stack and distinguish it from unaffiliated engagement farms."
  ∷ influence-acquisition locatePrimaryBannonLandCredit 96
    "Locate the primary interview, speech, recording or writing in which Bannon explicitly names Nick Land or Landian accelerationism, rather than relying on secondary influence attribution."
  ∷ influence-acquisition resolveForeignMemeFarmPartyCommissioning 92
    "Test for payment, instruction, shared assets, administrators, vendors or communications linking overseas pro-One-Nation engagement farms to official party actors."
  ∷ []
