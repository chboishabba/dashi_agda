module DASHI.Cognition.PalantirVoterDataAuthorityChain20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PalantirMissionExpansionContestability20261015Exact as Mission

------------------------------------------------------------------------
-- VOTER DATA AUTHORITY -> TRANSFER -> PROCESSING -> ELITE CHAIN — 2026-10-15
--
-- The point of this owner is to stop four distinct authority/action stages from
-- collapsing into one:
--   legal interpretation authorising acquisition/sharing
--   != actual DOJ->DHS transfer
--   != HSI/iLab processing/enrichment
--   != completed ingestion/use inside Palantir-supported ELITE.
------------------------------------------------------------------------

data AuthorityStage : Set where
  legalInterpretation : AuthorityStage
  dataAcquisition : AuthorityStage
  interagencyTransfer : AuthorityStage
  agencyProcessing : AuthorityStage
  pendingVendorSystemEntry : AuthorityStage
  completedSystemIngestion : AuthorityStage
  investigativeDecisionUse : AuthorityStage

record AuthorityReceipt : Set where
  constructor authority-receipt
  field
    label : String
    date : String
    source : String
    stage : AuthorityStage
    boundedFinding : String
    paid : Bool
open AuthorityReceipt public

olcOpinion20260512 : AuthorityReceipt
olcOpinion20260512 = authority-receipt
  "DOJ OLC voter-roll acquisition/sharing opinion"
  "2026-05-12"
  "U.S. Department of Justice, Office of Legal Counsel, 'Authority to Obtain and Share Statewide Voter Roll Data'"
  legalInterpretation
  "OLC publicly states that DOJ Civil Rights has authority to seek statewide voter lists and share them with DHS as part of identifying persons allegedly ineligible to vote. This pays the executive-branch legal interpretation and claimed authority surface, not a judicial merits ruling and not proof of any particular downstream Palantir ingestion."
  true

dojVoterRollAcquisition : AuthorityReceipt
dojVoterRollAcquisition = authority-receipt
  "DOJ voter-roll data available to HSI workflow"
  "2026"
  "ICE/HSI FOIA records and Democracy Forward public-record summary"
  dataAcquisition
  "The released HSI record set describes DOJ voting-roll data in the voter-fraud workflow and Democracy Forward reports approximately 50.6 million DOJ voter-roll records in the produced materials. Exact record-set provenance/state completeness remains a carrier-level acquisition task."
  true

hsiILabProcessing : AuthorityReceipt
hsiILabProcessing = authority-receipt
  "HSI iLab processing/enrichment"
  "2026-05 to 2026-07"
  "ICE/HSI FOIA emails"
  agencyProcessing
  "HSI records describe iLab processing DOJ voter rolls and USCIS data and later say six states were enriched by iLab. Processing/enrichment is paid as an agency workflow stage and remains distinct from completed ELITE ingestion."
  true

pendingPalantirEntry : AuthorityReceipt
pendingPalantirEntry = authority-receipt
  "Pending Palantir entry into ELITE"
  "2026-07"
  "ICE/HSI election-integrity report released by FOIA"
  pendingVendorSystemEntry
  "The report says Missouri, Michigan, New Mexico, Connecticut, Georgia and Kentucky had been enriched by iLab and were pending Palantir entry into ELITE. This is a near-deployment state, not completed system ingestion."
  true

record AuthorityChainBoundary : Set where
  constructor authority-chain-boundary
  field
    olcInterpretationPaid : Bool
    governmentDataAcquisitionPaid : Bool
    hsiProcessingPaid : Bool
    pendingPalantirEntryPaid : Bool
    completedELITEIngestionPaid : Bool
    individualInvestigativeUsePaid : Bool
    olcOpinionEqualsJudicialHolding : Bool
    authorityToShareImpliesDutyToIngest : Bool
    dataTransferImpliesPalantirControl : Bool
    processingImpliesEnforcementOutcome : Bool
open AuthorityChainBoundary public

canonicalAuthorityChainBoundary : AuthorityChainBoundary
canonicalAuthorityChainBoundary = authority-chain-boundary
  true true true true false false false false false false

data OLCOpinionImpliesJudicialHolding : Set where
data SharingAuthorityImpliesIngestion : Set where
data InteragencyDataImpliesVendorControl : Set where
data ProcessingImpliesEnforcement : Set where

olcDoesNotCreateJudicialHolding : OLCOpinionImpliesJudicialHolding → ⊥
olcDoesNotCreateJudicialHolding ()

sharingAuthorityDoesNotCreateIngestion : SharingAuthorityImpliesIngestion → ⊥
sharingAuthorityDoesNotCreateIngestion ()

interagencyDataDoesNotCreateVendorControl : InteragencyDataImpliesVendorControl → ⊥
interagencyDataDoesNotCreateVendorControl ()

processingDoesNotCreateEnforcement : ProcessingImpliesEnforcement → ⊥
processingDoesNotCreateEnforcement ()

------------------------------------------------------------------------
-- Max-cut: the missing bridge is no longer authority; it is execution/use.
------------------------------------------------------------------------

data AuthorityDebt : Set where
  exactDOJtoDHSDataTransferReceipts : AuthorityDebt
  exactFOIABatesMapping : AuthorityDebt
  eliteIngestionEndpoint : AuthorityDebt
  individualLeadDecisionUse : AuthorityDebt
  judicialReviewOfAuthority : AuthorityDebt

record AuthorityAcquisition : Set where
  constructor authority-acquisition
  field
    debt : AuthorityDebt
    priority : Nat
    instruction : String
open AuthorityAcquisition public

canonicalAuthorityAcquisition : List AuthorityAcquisition
canonicalAuthorityAcquisition =
  authority-acquisition exactFOIABatesMapping 100
    "Map the May/July ICE emails and election-integrity report to exact FOIA Bates/page identifiers so the chain rests on inspectable government carriers rather than quotations alone." ∷
  authority-acquisition eliteIngestionEndpoint 100
    "Resolve pending Palantir entry to actual ingestion, rejection/cancellation or technical deferral using ELITE audit/configuration/ingestion records; preserve Palantir's public no-integration statement meanwhile." ∷
  authority-acquisition exactDOJtoDHSDataTransferReceipts 99
    "Separate OLC authority from actual DOJ->DHS dataset transfer by acquiring transmittal logs, data-sharing records and dataset provenance for the voter-roll files used by HSI." ∷
  authority-acquisition individualLeadDecisionUse 99
    "Trace processed records to individual investigative leads, referrals, administrative/criminal action or closure on the same person/object; bulk processing alone is not enforcement." ∷
  authority-acquisition judicialReviewOfAuthority 98
    "Track court orders reviewing voter-data acquisition/sharing and state challenges separately from OLC's executive-branch interpretation."
  ∷ []
