module DASHI.Cognition.BannonCambridgeAnalyticaSystemicLeverageBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA
import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Systemic

------------------------------------------------------------------------
-- CAMBRIDGE ANALYTICA x SYSTEMIC LEVERAGE
--
-- Adds first/second/third-order incidence questions to the source-paid Bannon/
-- CA/SCL/Mercer infrastructure.  Beneficiary hypotheses are not motive claims.
------------------------------------------------------------------------

cambridgeAnalyticaFirstOrder : Systemic.SystemicLeverageCandidate
cambridgeAnalyticaFirstOrder = Systemic.systemic-leverage-candidate
  "Bannon / Cambridge Analytica / SCL / Mercer"
  Systemic.firstOrder
  Systemic.narrativeCapacity
  "How were platform-derived data, voter records and inferred personality/audience features converted into campaign targeting and message delivery?"
  "Which campaigns, vendors, donors or media organisations obtained targeting, fundraising, mobilisation or message-routing capability?"
  "Which data subjects and voters bore privacy, opacity, autonomy or information-asymmetry burdens?"
  "Who controlled data acquisition, model construction, audience definitions, creative selection, delivery and feedback?"
  "FTC enforcement record, FEC vendor/disbursement records, UK parliamentary evidence, platform records and campaign artefacts"
  true false false

cambridgeAnalyticaSecondOrder : Systemic.SystemicLeverageCandidate
cambridgeAnalyticaSecondOrder = Systemic.systemic-leverage-candidate
  "Bannon / Cambridge Analytica / SCL / Mercer"
  Systemic.secondOrder
  Systemic.accessBrokerage
  "How did a donor-financed data/communications firm alter the effective campaign capacity, cross-border introductions and media reach available to aligned political actors?"
  "Candidate beneficiaries include client campaigns, Mercer-backed political organisations, Cambridge Analytica/SCL and connected media/brokerage actors; each benefit magnitude remains independently source-dependent."
  "Potential burdens include campaign-finance transparency, privacy, competitors, non-targeted publics and people classified without meaningful knowledge or consent."
  "Who controlled vendor selection, common-vendor firewalls, donor routing, cross-border introductions and data/model access?"
  "FEC MUR files, corporate records, emails, contracts, invoices, campaign disclosures and parliamentary evidence"
  false false false

cambridgeAnalyticaThirdOrder : Systemic.SystemicLeverageCandidate
cambridgeAnalyticaThirdOrder = Systemic.systemic-leverage-candidate
  "Bannon / Cambridge Analytica / SCL / Mercer"
  Systemic.thirdOrder
  Systemic.institutionalControl
  "Did the influence stack alter later political-party infrastructure, media ecosystems, platform governance, privacy regulation or durable norms of campaign targeting?"
  "Who gained durable data, modelling, media, regulatory or agenda-setting option value after the immediate campaigns?"
  "Who bears long-run privacy, trust, democratic-legitimacy, platform-governance or chilling-effect costs?"
  "Which resulting institutions and technical systems are auditable, contestable, reversible or practically escapable?"
  "post-2018 regulation/enforcement, platform-policy changes, successor organisations, campaign vendor lineages and longitudinal political-media records"
  false false false

record CambridgeAnalyticaSystemicBoundary : Set where
  constructor cambridge-analytica-systemic-boundary
  field
    dataToTargetingLoopPaid : Bool
    crossBorderBrokeragePaid : Bool
    trumpCampaignVendorScalePaid : Bool
    commonVendorTopologyPaid : Bool
    downstreamSystemicEffectsWorthAcquiring : Bool
    donorBenefitMagnitudeResolved : Bool
    universalPsychographicPersuasionResolved : Bool
    electionCausationResolved : Bool
    laterEpsteinTechniqueReuseResolved : Bool
open CambridgeAnalyticaSystemicBoundary public

canonicalCambridgeAnalyticaSystemicBoundary : CambridgeAnalyticaSystemicBoundary
canonicalCambridgeAnalyticaSystemicBoundary = cambridge-analytica-systemic-boundary
  true true true true true false false false false

caSourceBoundary : CA.BannonInfluenceInfrastructureBoundary
caSourceBoundary = CA.canonicalBannonInfluenceInfrastructureBoundary

data DonorFundingImpliesCampaignControl : Set where
data TargetingInfrastructureImpliesOutcomeControl : Set where
data HistoricalCapabilityImpliesLaterReuse : Set where

donorFundingDoesNotCreateCampaignControl : DonorFundingImpliesCampaignControl → ⊥
donorFundingDoesNotCreateCampaignControl ()

targetingInfrastructureDoesNotCreateOutcomeControl : TargetingInfrastructureImpliesOutcomeControl → ⊥
targetingInfrastructureDoesNotCreateOutcomeControl ()

historicalCapabilityDoesNotCreateLaterReuse : HistoricalCapabilityImpliesLaterReuse → ⊥
historicalCapabilityDoesNotCreateLaterReuse ()
