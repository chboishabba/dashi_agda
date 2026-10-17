module DASHI.Cognition.EpsteinFinanceTechParetoRoundExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinCorporateBoardNetworkAcquisitionExact as Corporate

------------------------------------------------------------------------
-- FINANCE / TECH PARETO ACQUISITION ROUND
--
-- This round is source-led. Candidate nomination can come from the CESifo
-- corporate atlas, Senate Finance transactional lists, high-quality tech
-- reporting, DOJ search, or public indexes. Promotion still requires an
-- edge-local record appropriate to the claim.
------------------------------------------------------------------------

data CandidateLane : Set where
  senateFinanceTransactionalAtlas : CandidateLane
  sp500BoardContactAtlas : CandidateLane
  bigTechDirectCorrespondence : CandidateLane
  thielValarBarakPalantir : CandidateLane
  hoffmanItoMediaLab : CandidateLane
  brinPageGoogle : CandidateLane
  sinofskyMicrosoft : CandidateLane
  muskSolarCity : CandidateLane
  ellisonOracleMediaInfrastructure : CandidateLane
  andrewTradePublicOffice : CandidateLane
  bankEnablement : CandidateLane

record CandidateStatus : Set where
  constructor candidate-status
  field
    lane : CandidateLane
    publicSourceSupport : Bool
    primaryOrGovernmentSurfaceAvailable : Bool
    directContactAlreadySupported : Bool
    transactionOrInstitutionalEdgeSupported : Bool
    wrongdoingEstablishedByThisStatus : Bool
    acquisitionInstruction : String
open CandidateStatus public

senateFinanceStatus : CandidateStatus
senateFinanceStatus = candidate-status
  senateFinanceTransactionalAtlas true true false true false
  "Use Senate Finance Treasury-record lists as an official transaction-oriented candidate atlas; resolve each named entity to the underlying SAR, wire, account, lawsuit or institutional record before making person-level claims."

sp500Status : CandidateStatus
sp500Status = candidate-status
  sp500BoardContactAtlas true false false false false
  "Use the Gertsberg-Pagel-Volkova board atlas to rank corporate candidates; re-resolve every promoted contact to the underlying DOJ document because LLM classification is not itself the primary receipt."

bigTechStatus : CandidateStatus
bigTechStatus = candidate-status
  bigTechDirectCorrespondence true true true false false
  "Prioritise tech figures for whom released records show direct correspondence or explicit meetings rather than ranking by mention count alone."

thielStatus : CandidateStatus
thielStatus = candidate-status
  thielValarBarakPalantir true true true true false
  "Resolve direct Epstein-Thiel scheduling/correspondence, Valar transactions, Barak introductions and Palantir references as distinct edges; do not collapse business overlap into coordination."

hoffmanStatus : CandidateStatus
hoffmanStatus = candidate-status
  hoffmanItoMediaLab true true true true false
  "Expand the Hoffman-Ito-Media Lab fundraising/convening path through exact meetings, travel, fundraising asks and institutional records."

brinPageStatus : CandidateStatus
brinPageStatus = candidate-status
  brinPageGoogle true true true false false
  "Resolve Brin/Page correspondence, meetings and referrals separately; subpoenas or third-party mentions are not themselves proof of direct contact."

sinofskyStatus : CandidateStatus
sinofskyStatus = candidate-status
  sinofskyMicrosoft true true true false false
  "Acquire the direct advisory/correspondence chain and distinguish personal career advice from Microsoft institutional involvement."

muskStatus : CandidateStatus
muskStatus = candidate-status
  muskSolarCity true true true false false
  "Resolve direct correspondence and SolarCity/business references while keeping proposed travel, actual travel and wrongdoing as separate questions."

ellisonStatus : CandidateStatus
ellisonStatus = candidate-status
  ellisonOracleMediaInfrastructure true false false false false
  "Treat Ellison as a black-book/media-infrastructure candidate: acquire the original address-book page and any direct-contact record before promoting a personal relationship; separately study Paramount/CBS/Oracle media ownership and post-Epstein information-governance controversies as modern context, not retroactive Epstein contact."

andrewStatus : CandidateStatus
andrewStatus = candidate-status
  andrewTradePublicOffice true true true true false
  "Track the 2026 misconduct-in-public-office investigation and alleged trade-information disclosure separately from earlier social/sexual-abuse allegations and civil settlement; investigation is not conviction."

bankStatus : CandidateStatus
bankStatus = candidate-status
  bankEnablement true true false true false
  "Prioritise JPMorgan, Deutsche Bank, Bank of America and other transaction processors using Senate Finance findings, SAR chronology, settlements and underlying records; distinguish committee allegations/findings, civil settlements, bank admissions and adjudicated violations."

currentRound : List CandidateStatus
currentRound =
  senateFinanceStatus ∷ sp500Status ∷ thielStatus ∷ hoffmanStatus ∷
  bankStatus ∷ bigTechStatus ∷ brinPageStatus ∷ sinofskyStatus ∷
  muskStatus ∷ andrewStatus ∷ ellisonStatus ∷ []

------------------------------------------------------------------------
-- Cross-owner acquisition receipt.
------------------------------------------------------------------------

corporateFreshSweepRequired :
  Corporate.freshWebSweepRequired Corporate.canonicalRoundRule ≡ true
corporateFreshSweepRequired = refl

aiModeCannotPromoteEdge :
  Corporate.aiModeLeadCanPromoteEdgeWithoutVerification Corporate.canonicalRoundRule ≡ false
aiModeCannotPromoteEdge = refl

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data MentionCountCreatesRelationship : Set where
data BlackBookCreatesMutualContact : Set where
data InvestigationCreatesConviction : Set where
data CivilSettlementCreatesAdmission : Set where
data GovernmentCandidateListCreatesWrongdoing : Set where
data BusinessOverlapCreatesCoordination : Set where

mentionCountDoesNotCreateRelationship : MentionCountCreatesRelationship → ⊥
mentionCountDoesNotCreateRelationship ()

blackBookDoesNotCreateMutualContact : BlackBookCreatesMutualContact → ⊥
blackBookDoesNotCreateMutualContact ()

investigationDoesNotCreateConviction : InvestigationCreatesConviction → ⊥
investigationDoesNotCreateConviction ()

civilSettlementDoesNotCreateAdmission : CivilSettlementCreatesAdmission → ⊥
civilSettlementDoesNotCreateAdmission ()

governmentCandidateListDoesNotCreateWrongdoing : GovernmentCandidateListCreatesWrongdoing → ⊥
governmentCandidateListDoesNotCreateWrongdoing ()

businessOverlapDoesNotCreateCoordination : BusinessOverlapCreatesCoordination → ⊥
businessOverlapDoesNotCreateCoordination ()
