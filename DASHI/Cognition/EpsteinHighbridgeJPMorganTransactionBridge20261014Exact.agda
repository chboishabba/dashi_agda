module DASHI.Cognition.EpsteinHighbridgeJPMorganTransactionBridge20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- HIGHBRIDGE / JPMORGAN / FINANCIAL TRUST TRANSACTION BRIDGE — 2026-10-14
--
-- This owner separates four economically different objects:
--   1. Epstein/Financial Trust as Highbridge consultant;
--   2. the USD15m merger/acquisition-advice payment tied to JPMorgan's
--      acquisition of a majority interest in Highbridge;
--   3. Financial Trust/Haze/Southern Financial as Highbridge investors;
--   4. JPMorgan as transaction acquirer/bank rather than payer of the fee.
------------------------------------------------------------------------

data HighbridgeSurface : Set where
  consultingRetainer : HighbridgeSurface
  mergerAcquisitionAdviceFee : HighbridgeSurface
  fundInvestment : HighbridgeSurface
  fundRedemption : HighbridgeSurface
  bankAcquisition : HighbridgeSurface
  bankerIntroductionHypothesis : HighbridgeSurface

record HighbridgeReceipt : Set where
  constructor highbridge-receipt
  field
    label : String
    source : String
    surface : HighbridgeSurface
    boundedFinding : String
    amountUSD : Nat
    paid : Bool
    wrongdoingPaid : Bool
open HighbridgeReceipt public

highbridgeConsultingAgreement : HighbridgeReceipt
highbridgeConsultingAgreement = highbridge-receipt
  "Highbridge-Financial Trust consulting agreement"
  "EFTA00589969; USVI v JPMorgan court exhibits"
  consultingRetainer
  "A revised consulting agreement effective 1 June 2005 engages Financial Trust Company as consultant to Highbridge Capital Management and assigns Jeffrey Epstein to perform the specified services. Released copies identify Glenn Dubin for Highbridge and Epstein for Financial Trust."
  0 true false

highbridge2004Fee : HighbridgeReceipt
highbridge2004Fee = highbridge-receipt
  "USD15m Highbridge acquisition-related fee"
  "USVI v JPMorgan, Document 284-5 / JPMC Exhibits 194-195 / EFTA02816421"
  mergerAcquisitionAdviceFee
  "Court filings state Dubin & Swieca Holdings paid Financial Trust Company USD15m related to JPMorgan's 2004 acquisition of a majority interest in Highbridge; the invoice describes merger-and-acquisition advice. The same filings state JPMorgan itself did not pay Epstein this fee."
  15000000 true false

financialTrustHighbridgeRedemption2006 : HighbridgeReceipt
financialTrustHighbridgeRedemption2006 = highbridge-receipt
  "Financial Trust Highbridge redemption"
  "EFTA00614037..44"
  fundRedemption
  "Highbridge documentation records Financial Trust Company redemption activity, including a January 2006 USD25m redemption acknowledgement and an August 2006 instruction to liquidate its entire Highbridge Long/Short Equity Fund interest. These are investor/redemption edges distinct from consulting compensation."
  25000000 true false

hazeRedemption2014 : HighbridgeReceipt
hazeRedemption2014 = highbridge-receipt
  "Haze Highbridge 2014 redemption"
  "EFTA01118143 valuation report"
  fundRedemption
  "Epstein-family-office valuation records show a USD38,485,360 Highbridge redemption attributed to Haze in October 2014. Gross redemption proceeds are not profit without contribution/distribution history."
  38485360 true false

southernFinancialRedemption2014 : HighbridgeReceipt
southernFinancialRedemption2014 = highbridge-receipt
  "Southern Financial Highbridge 2014 redemption"
  "EFTA01118143 valuation report"
  fundRedemption
  "The same October 2014 report records USD20,785,189 of Highbridge redemption proceeds to Southern Financial LLC. This is separate from the USD15m 2004 advisory fee and from Haze's redemption."
  20785189 true false

record HighbridgeBoundary : Set where
  constructor highbridge-boundary
  field
    financialTrustWasHighbridgeConsultant : Bool
    acquisitionRelatedFeePaid : Bool
    jpmorganWasFeePayer : Bool
    epsteinEntitiesWereHighbridgeInvestors : Bool
    consultingFeeEqualsInvestmentCapital : Bool
    redemptionProceedsEqualProfit : Bool
    highbridgeRelationshipImpliesJPMorganDirectedEpstein : Bool
    allegedIntroductionImpliesProvedIntroduction : Bool
open HighbridgeBoundary public

canonicalHighbridgeBoundary : HighbridgeBoundary
canonicalHighbridgeBoundary = highbridge-boundary
  true true false true false false false false

data JPMorganAcquisitionImpliesJPMorganPaidFee : Set where
data ConsultingFeeImpliesFundCapital : Set where
data GrossRedemptionImpliesProfit : Set where
data TransactionContextImpliesBankCommand : Set where
data ReportedIntroductionImpliesPrimaryReceipt : Set where

jpmorganAcquisitionDoesNotCreateFeePayer : JPMorganAcquisitionImpliesJPMorganPaidFee → ⊥
jpmorganAcquisitionDoesNotCreateFeePayer ()

consultingFeeDoesNotCreateFundCapital : ConsultingFeeImpliesFundCapital → ⊥
consultingFeeDoesNotCreateFundCapital ()

grossRedemptionDoesNotCreateProfit : GrossRedemptionImpliesProfit → ⊥
grossRedemptionDoesNotCreateProfit ()

transactionContextDoesNotCreateBankCommand : TransactionContextImpliesBankCommand → ⊥
transactionContextDoesNotCreateBankCommand ()

reportedIntroductionDoesNotCreatePrimaryReceipt : ReportedIntroductionImpliesPrimaryReceipt → ⊥
reportedIntroductionDoesNotCreatePrimaryReceipt ()

------------------------------------------------------------------------
-- Pareto acquisition.
------------------------------------------------------------------------

data HighbridgeDebt : Set where
  exact2004InvoiceAndWire : HighbridgeDebt
  transactionWorkProduct : HighbridgeDebt
  dubinSwiecaDecisionChain : HighbridgeDebt
  staleyIntroductionReceipt : HighbridgeDebt
  completeContributionHistory : HighbridgeDebt
  realisedReturnLedger : HighbridgeDebt
  jpmorganDealDocumentRole : HighbridgeDebt

record HighbridgeAcquisition : Set where
  constructor highbridge-acquisition
  field
    debt : HighbridgeDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open HighbridgeAcquisition public

canonicalHighbridgeAcquisition : List HighbridgeAcquisition
canonicalHighbridgeAcquisition =
  highbridge-acquisition exact2004InvoiceAndWire 100 true
    "Acquire and bind the December 2004 Financial Trust invoice and processed USD15m wire as exact primary objects, including originating account/entity and Bear Stearns settlement route."
  ∷ highbridge-acquisition transactionWorkProduct 100 true
    "Recover the actual merger/acquisition advice, introductions, analyses or deliverables for which the USD15m was paid; invoice description alone does not measure work performed."
  ∷ highbridge-acquisition dubinSwiecaDecisionChain 99 true
    "Resolve who at Dubin & Swieca/Highbridge approved the fee, why, and how it was booked, including any internal disagreement about purpose."
  ∷ highbridge-acquisition staleyIntroductionReceipt 99 true
    "Test the reported Epstein->Dubin/Staley introduction story against calendars, email, deal documents and testimony; preserve source conflict until an edge-local receipt pays it."
  ∷ highbridge-acquisition jpmorganDealDocumentRole 98 true
    "Resolve Epstein/Financial Trust's exact role in the Highbridge-JPMorgan transaction documents and distinguish adviser listing from decision authority."
  ∷ highbridge-acquisition completeContributionHistory 97 true
    "Reconstruct each Epstein-controlled entity's Highbridge contributions, transfers and withdrawals from inception rather than deriving capital from the 2004 fee."
  ∷ highbridge-acquisition realisedReturnLedger 96 true
    "Compute realised Highbridge returns only after complete contribution/distribution/fee history; redemption proceeds alone are not gain."
  ∷ []
