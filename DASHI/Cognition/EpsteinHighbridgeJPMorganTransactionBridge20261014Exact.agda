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
-- This owner separates five economically different objects:
--   1. a proposed 2005 Financial Trust/Highbridge consulting retainer;
--   2. an exact USD15m merger/acquisition-advice invoice and processed wire
--      tied to JPMorgan's 2004 acquisition of a majority Highbridge interest;
--   3. Financial Trust/Haze/Southern Financial as Highbridge investors;
--   4. later redemption proceeds, which are not profits by themselves;
--   5. JPMorgan as transaction acquirer rather than payer of the USD15m fee.
------------------------------------------------------------------------

data HighbridgeSurface : Set where
  proposedConsultingRetainer : HighbridgeSurface
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
    relationPaid : Bool
    cashPaymentPaid : Bool
    wrongdoingPaid : Bool
open HighbridgeReceipt public

highbridgeConsultingDraft : HighbridgeReceipt
highbridgeConsultingDraft = highbridge-receipt
  "Highbridge-Financial Trust proposed 2005 consulting retainer"
  "EFTA00589969 / EFTA01581710..13"
  proposedConsultingRetainer
  "A revised consulting agreement effective 1 June 2005 proposes Financial Trust Company as consultant to Highbridge Capital Management, assigns Jeffrey Epstein to perform contemplated services, and specifies USD2.25m over five annual USD450k installments plus qualified-fund investment terms. The publicly released signature lines for Glenn Dubin and Jeffrey Epstein are blank and no matching installment-payment ledger was located in this round, so the proposed retainer terms are paid but realised retainer revenue is not."
  2250000 true false false

highbridge2004Invoice : HighbridgeReceipt
highbridge2004Invoice = highbridge-receipt
  "28 December 2004 USD15m M&A-advice invoice"
  "JPM-SDNY-00061108 / EFTA01581709 / court Exhibit 246 lineage"
  mergerAcquisitionAdviceFee
  "Financial Trust Company invoiced Highbridge's Ron Resnick USD15m for 'Fees for merger and acquisition advice'. The released invoice carries a handwritten approval-to-pay notation."
  15000000 true false false

highbridge2004ProcessedWire : HighbridgeReceipt
highbridge2004ProcessedWire = highbridge-receipt
  "29 December 2004 processed USD15m wire"
  "JPM-SDNY-00061107 / EFTA01581708 / USVI v JPMorgan Exhibit 246"
  mergerAcquisitionAdviceFee
  "A next-day domestic wire confirmation marked processed records USD15m to Bear Stearns & Company for further credit to Financial Trust Company. Court filings identify Dubin & Swieca Holdings as payer and tie the fee to JPMorgan's acquisition of a majority interest in Highbridge."
  15000000 true true false

jpmorganNotFeePayer : HighbridgeReceipt
jpmorganNotFeePayer = highbridge-receipt
  "JPMorgan acquisition / fee-payer scope boundary"
  "USVI v JPMorgan Document 284-5 / JPMC admissions and testimony"
  bankAcquisition
  "Court filings state Financial Trust received the USD15m fee from Dubin & Swieca Holdings related to the Highbridge acquisition and that Epstein did not receive the fee from JPMorgan itself."
  0 true false false

financialTrustHighbridgeRedemption2006 : HighbridgeReceipt
financialTrustHighbridgeRedemption2006 = highbridge-receipt
  "Financial Trust Highbridge redemption"
  "EFTA00614037..44"
  fundRedemption
  "Highbridge documentation records Financial Trust Company redemption activity, including a January 2006 USD25m redemption acknowledgement and an August 2006 instruction to liquidate its entire Highbridge Long/Short Equity Fund interest. These are investor/redemption edges distinct from consulting compensation."
  25000000 true true false

hazeRedemption2014 : HighbridgeReceipt
hazeRedemption2014 = highbridge-receipt
  "Haze Highbridge 2014 redemption"
  "EFTA01118143 valuation report"
  fundRedemption
  "Epstein-family-office valuation records show USD38,485,360 of Highbridge redemption proceeds attributed to Haze in October 2014. Gross redemption proceeds are not profit without contribution/distribution history."
  38485360 true true false

southernFinancialRedemption2014 : HighbridgeReceipt
southernFinancialRedemption2014 = highbridge-receipt
  "Southern Financial Highbridge 2014 redemption"
  "EFTA01118143 valuation report"
  fundRedemption
  "The same October 2014 report records USD20,785,189 of Highbridge redemption proceeds to Southern Financial LLC. This is separate from the USD15m 2004 advisory fee and from Haze's redemption."
  20785189 true true false

record HighbridgeBoundary : Set where
  constructor highbridge-boundary
  field
    proposedRetainerTermsPaid : Bool
    proposedRetainerCashPaid : Bool
    acquisitionRelatedInvoicePaid : Bool
    acquisitionRelatedWirePaid : Bool
    jpmorganWasFeePayer : Bool
    epsteinEntitiesWereHighbridgeInvestors : Bool
    consultingFeeEqualsInvestmentCapital : Bool
    redemptionProceedsEqualProfit : Bool
    highbridgeRelationshipImpliesJPMorganDirectedEpstein : Bool
    allegedIntroductionImpliesProvedIntroduction : Bool
open HighbridgeBoundary public

canonicalHighbridgeBoundary : HighbridgeBoundary
canonicalHighbridgeBoundary = highbridge-boundary
  true false true true false true false false false false

data JPMorganAcquisitionImpliesJPMorganPaidFee : Set where
data ConsultingFeeImpliesFundCapital : Set where
data GrossRedemptionImpliesProfit : Set where
data TransactionContextImpliesBankCommand : Set where
data ReportedIntroductionImpliesPrimaryReceipt : Set where
data UnsignedDraftImpliesCashRevenue : Set where

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

unsignedDraftDoesNotCreateCashRevenue : UnsignedDraftImpliesCashRevenue → ⊥
unsignedDraftDoesNotCreateCashRevenue ()

------------------------------------------------------------------------
-- Pareto acquisition after exact invoice/wire closure.
------------------------------------------------------------------------

data HighbridgeDebt : Set where
  transactionWorkProduct : HighbridgeDebt
  dubinSwiecaDecisionChain : HighbridgeDebt
  staleyIntroductionReceipt : HighbridgeDebt
  consultingRetainerPerformance : HighbridgeDebt
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
  highbridge-acquisition transactionWorkProduct 100 true
    "Recover the actual merger/acquisition advice, introductions, analyses or deliverables for which the exact USD15m invoice/wire was paid; invoice description establishes stated purpose, not work-product quality or value."
  ∷ highbridge-acquisition dubinSwiecaDecisionChain 100 true
    "Resolve who at Dubin & Swieca/Highbridge approved the USD15m fee, why, how it was booked and any internal disagreement about its purpose."
  ∷ highbridge-acquisition staleyIntroductionReceipt 100 true
    "Test the reported Epstein->Dubin/Staley introduction story against calendars, email, deal documents and testimony; preserve source conflict until an edge-local receipt pays it."
  ∷ highbridge-acquisition jpmorganDealDocumentRole 99 true
    "Resolve Epstein/Financial Trust's exact role in the Highbridge-JPMorgan transaction documents and distinguish adviser listing from decision authority."
  ∷ highbridge-acquisition consultingRetainerPerformance 98 true
    "Determine whether the unsigned 2005 USD2.25m retainer draft was executed in another copy and whether any USD450k installments were actually paid."
  ∷ highbridge-acquisition completeContributionHistory 97 true
    "Reconstruct each Epstein-controlled entity's Highbridge contributions, transfers and withdrawals from inception rather than deriving capital from the 2004 fee."
  ∷ highbridge-acquisition realisedReturnLedger 96 true
    "Compute realised Highbridge returns only after complete contribution/distribution/fee history; redemption proceeds alone are not gain."
  ∷ []
