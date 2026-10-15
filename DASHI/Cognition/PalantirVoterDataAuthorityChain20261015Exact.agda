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
  "ICE/HSI FOIA 2026-ICLI-00100 first interim production; Democracy Forward public-record summary"
  dataAcquisition
  "The released HSI record set describes DOJ voting-roll data in the voter-fraud workflow and Democracy Forward reports approximately 50.6 million DOJ voter-roll records in the produced materials. Exact dataset provenance/state completeness remains distinct from the aggregate figure."
  true

hsiILabProcessing : AuthorityReceipt
hsiILabProcessing = authority-receipt
  "HSI iLab processing/enrichment"
  "2026-05 to 2026-07"
  "ICE FOIA 2026-ICLI-00100 first interim production"
  agencyProcessing
  "HSI records describe iLab processing DOJ voter rolls and USCIS data and later say six states were enriched by iLab. Processing/enrichment is paid as an agency workflow stage and remains distinct from completed ELITE ingestion."
  true

pendingPalantirEntry : AuthorityReceipt
pendingPalantirEntry = authority-receipt
  "Pending Palantir entry into ELITE"
  "2026-07-06"
  "ICE FOIA 2026-ICLI-00100 first interim production, Bates 2026-ICLI-00100 140"
  pendingVendorSystemEntry
  "Public indexing of ICE's released first-interim production identifies Bates 140 as the first page of the 6 July HSI election-integrity report. Under iLab State Processing it states that MO, MI, NM, CT, GA and KY had been enriched by iLab and were pending Palantir entry into ELITE; Michigan and New Mexico were pending legal review. Carrier identity and Bates mapping are paid, while direct page inspection and the later ingestion endpoint remain open."
  true

record FOIACarrierReceipt : Set where
  constructor foia-carrier-receipt
  field
    requestId : String
    litigation : String
    productionPages : Nat
    releaseDate : String
    julyReportBates : String
    carrierIdentityPaid : Bool
    exactBatesMappingPaid : Bool
    fullProductionDirectlyInspectedInThisRound : Bool
open FOIACarrierReceipt public

canonicalFOIACarrier : FOIACarrierReceipt
canonicalFOIACarrier = foia-carrier-receipt
  "2026-ICLI-00100"
  "Democracy Forward Foundation v. DHS, 1:26-cv-02624-BAH"
  166
  "2026-10-07 public release; ICE production dated/released 2026-10-01 in public indexing"
  "2026-ICLI-00100 140"
  true true false

record AuthorityChainBoundary : Set where
  constructor authority-chain-boundary
  field
    olcInterpretationPaid : Bool
    governmentDataAcquisitionPaid : Bool
    hsiProcessingPaid : Bool
    pendingPalantirEntryPaid : Bool
    exactFOIACarrierAndJulyBatesPaid : Bool
    completedELITEIngestionPaid : Bool
    individualInvestigativeUsePaid : Bool
    olcOpinionEqualsJudicialHolding : Bool
    authorityToShareImpliesDutyToIngest : Bool
    dataTransferImpliesPalantirControl : Bool
    processingImpliesEnforcementOutcome : Bool
open AuthorityChainBoundary public

canonicalAuthorityChainBoundary : AuthorityChainBoundary
canonicalAuthorityChainBoundary = authority-chain-boundary
  true true true true true false false false false false false

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
-- Max-cut: the missing bridge is now execution/use, not carrier discovery.
------------------------------------------------------------------------

data AuthorityDebt : Set where
  fullFOIAProductionDirectInspection : AuthorityDebt
  exactDOJtoDHSDataTransferReceipts : AuthorityDebt
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
  authority-acquisition eliteIngestionEndpoint 100
    "Resolve Bates-140 pending Palantir entry to actual ingestion, rejection/cancellation or technical deferral using ELITE audit/configuration/ingestion records; preserve Palantir's public no-integration statement meanwhile." ∷
  authority-acquisition fullFOIAProductionDirectInspection 100
    "Acquire the complete 166-page 2026-ICLI-00100 first-interim production and directly inspect Bates 140 plus the May processing emails so exact quotations/context no longer depend on public indexing/reporting mirrors." ∷
  authority-acquisition exactDOJtoDHSDataTransferReceipts 99
    "Separate OLC authority from actual DOJ->DHS dataset transfer by acquiring transmittal logs, data-sharing records and dataset provenance for the voter-roll files used by HSI." ∷
  authority-acquisition individualLeadDecisionUse 99
    "Trace processed records to individual investigative leads, referrals, administrative/criminal action or closure on the same person/object; bulk processing alone is not enforcement." ∷
  authority-acquisition judicialReviewOfAuthority 98
    "Track court orders reviewing voter-data acquisition/sharing and state challenges separately from OLC's executive-branch interpretation."
  ∷ []
