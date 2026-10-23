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
-- Source classes are deliberately separated:
--   * exact invoice/wire records;
--   * Epstein's sworn 2011 first-person deposition testimony;
--   * contemporaneous/post-deal JPMorgan email exhibits;
--   * USVI litigation allegations/characterisations;
--   * secondary reporting.
--
-- First-person testimony pays what Epstein claimed/remembered. Litigation
-- allegations remain allegations. Neither alone creates adjudicated sole
-- causation of JPMorgan's Highbridge acquisition.
------------------------------------------------------------------------

data HighbridgeSurface : Set where
  proposedConsultingRetainer : HighbridgeSurface
  mergerAcquisitionAdviceFee : HighbridgeSurface
  fundInvestment : HighbridgeSurface
  fundRedemption : HighbridgeSurface
  bankAcquisition : HighbridgeSurface
  financingApproach : HighbridgeSurface
  directIntroductionClaim : HighbridgeSurface
  postDealInformationLoop : HighbridgeSurface
  litigationBrokerageAllegation : HighbridgeSurface

record HighbridgeReceipt : Set where
  constructor highbridge-receipt
  field
    label : String
    source : String
    sourceClass : String
    surface : HighbridgeSurface
    boundedFinding : String
    amountUSD : Nat
    relationPaid : Bool
    cashPaymentPaid : Bool
    independentCausationPaid : Bool
    wrongdoingPaid : Bool
open HighbridgeReceipt public

highbridgeConsultingDraft : HighbridgeReceipt
highbridgeConsultingDraft = highbridge-receipt
  "Highbridge-Financial Trust proposed 2005 consulting retainer"
  "EFTA00589969 / EFTA01581710..13"
  "released draft contract"
  proposedConsultingRetainer
  "A revised consulting agreement effective 1 June 2005 proposes Financial Trust Company as consultant to Highbridge Capital Management, assigns Jeffrey Epstein to perform contemplated services, and specifies USD2.25m over five annual USD450k installments plus qualified-fund investment terms. Publicly released signature lines are blank and no matching installment-payment ledger was located, so proposed retainer terms are paid but realised retainer revenue is not."
  2250000 true false false false

highbridge2004Invoice : HighbridgeReceipt
highbridge2004Invoice = highbridge-receipt
  "28 December 2004 USD15m M&A-advice invoice"
  "JPM-SDNY-00061108 / EFTA01581709 / court Exhibit 246 lineage"
  "primary transaction document"
  mergerAcquisitionAdviceFee
  "Financial Trust Company invoiced Highbridge's Ron Resnick USD15m for 'Fees for merger and acquisition advice'. The released invoice carries a handwritten approval-to-pay notation."
  15000000 true false false false

highbridge2004ProcessedWire : HighbridgeReceipt
highbridge2004ProcessedWire = highbridge-receipt
  "29 December 2004 processed USD15m wire"
  "JPM-SDNY-00061107 / EFTA01581708 / USVI v JPMorgan Exhibit 246"
  "primary processed wire"
  mergerAcquisitionAdviceFee
  "A next-day domestic wire confirmation marked processed records USD15m to Bear Stearns & Company for further credit to Financial Trust Company. Court filings identify Dubin & Swieca Holdings as payer and tie the fee to JPMorgan's acquisition of a majority interest in Highbridge."
  15000000 true true false false

jpmorganNotFeePayer : HighbridgeReceipt
jpmorganNotFeePayer = highbridge-receipt
  "JPMorgan acquisition / fee-payer scope boundary"
  "USVI v JPMorgan Document 284-5 / JPMC admissions and testimony"
  "party admission / litigation record"
  bankAcquisition
  "Court filings state Financial Trust received the USD15m fee from Dubin & Swieca Holdings related to the Highbridge acquisition and that Epstein did not receive the fee from JPMorgan itself."
  0 true false false false

epsteinFinancingApproach2011Deposition : HighbridgeReceipt
epsteinFinancingApproach2011Deposition = highbridge-receipt
  "Epstein sworn account of approaching JPMorgan/Staley for Highbridge financing"
  "EFTA00299085, deposition pp.81-86"
  "sworn first-person deposition testimony"
  financingApproach
  "Epstein testified in 2011 that in roughly 2003 he considered purchasing Highbridge himself, went to JPMorgan and Jes Staley to seek financing, and then learned that Highbridge and JPMorgan met and pursued a joint-venture/purchase structure instead. He identified Glenn Dubin as the Highbridge participant and Staley as the JPMorgan participant. This pays Epstein's sworn account, not independent proof that his approach caused the bank's acquisition."
  0 true false false false

epsteinIntroductionClaim2011Deposition : HighbridgeReceipt
epsteinIntroductionClaim2011Deposition = highbridge-receipt
  "Epstein sworn introduction/fee account"
  "EFTA00299085, deposition pp.93-98"
  "sworn first-person deposition testimony"
  directIntroductionClaim
  "Epstein testified that he had discussed buying Highbridge with Dubin before he introduced Dubin to Staley, and that Dubin later came to Epstein's house and said Epstein should receive a fee for the introduction. Epstein identified the USD15m Financial Trust invoice as the fee connected to the deal. This is strong first-person evidence of claimed brokerage but not independent adjudication of sole causal responsibility for the transaction."
  15000000 true true false false

usviBrokerageAllegation : HighbridgeReceipt
usviBrokerageAllegation = highbridge-receipt
  "USVI Highbridge brokerage allegation"
  "USVI v JPMorgan filings including EFTA00145666 / complaint and summary-judgment record"
  "plaintiff litigation allegation/characterisation"
  litigationBrokerageAllegation
  "The US Virgin Islands alleged that Epstein introduced Staley to Dubin and facilitated JPMorgan's Highbridge acquisition. This is an attributed litigation allegation supported by cited exhibits; it is not an adjudicated finding simply because it appears in a court filing."
  0 true false false false

staleyPostDealBCC : HighbridgeReceipt
staleyPostDealBCC = highbridge-receipt
  "Staley post-deal Highbridge email blind-copy to Epstein"
  "USVI v JPMorgan Document 285-2, Ex.245 description"
  "primary-email exhibit described in court filing"
  postDealInformationLoop
  "After the Highbridge acquisition, Staley blind-copied Epstein on a June 2005 draft email to JPMorgan committees, Jamie Dimon and Glenn Dubin praising Highbridge integration. This pays post-deal informational inclusion/proximity; it does not prove decision authority or a continuing formal advisory role."
  0 true false false false

financialTrustHighbridgeRedemption2006 : HighbridgeReceipt
financialTrustHighbridgeRedemption2006 = highbridge-receipt
  "Financial Trust Highbridge redemption"
  "EFTA00614037..44"
  "fund record"
  fundRedemption
  "Highbridge documentation records Financial Trust Company redemption activity, including a January 2006 USD25m redemption acknowledgement and an August 2006 instruction to liquidate its entire Highbridge Long/Short Equity Fund interest. These are investor/redemption edges distinct from consulting compensation."
  25000000 true true false false

hazeRedemption2014 : HighbridgeReceipt
hazeRedemption2014 = highbridge-receipt
  "Haze Highbridge 2014 redemption"
  "EFTA01118143 valuation report"
  "family-office accounting record"
  fundRedemption
  "Epstein-family-office valuation records show USD38,485,360 of Highbridge redemption proceeds attributed to Haze in October 2014. Gross redemption proceeds are not profit without contribution/distribution history."
  38485360 true true false false

southernFinancialRedemption2014 : HighbridgeReceipt
southernFinancialRedemption2014 = highbridge-receipt
  "Southern Financial Highbridge 2014 redemption"
  "EFTA01118143 valuation report"
  "family-office accounting record"
  fundRedemption
  "The same October 2014 report records USD20,785,189 of Highbridge redemption proceeds to Southern Financial LLC. This is separate from the USD15m 2004 advisory fee and from Haze's redemption."
  20785189 true true false false

record HighbridgeBoundary : Set where
  constructor highbridge-boundary
  field
    proposedRetainerTermsPaid : Bool
    proposedRetainerCashPaid : Bool
    acquisitionRelatedInvoicePaid : Bool
    acquisitionRelatedWirePaid : Bool
    epsteinSwornBrokerageClaimPaid : Bool
    postDealBCCPaid : Bool
    usviBrokerageAllegationPaidAsAllegation : Bool
    independentSoleCausationPaid : Bool
    jpmorganWasFeePayer : Bool
    epsteinEntitiesWereHighbridgeInvestors : Bool
    consultingFeeEqualsInvestmentCapital : Bool
    redemptionProceedsEqualProfit : Bool
    highbridgeRelationshipImpliesJPMorganDirectedEpstein : Bool
open HighbridgeBoundary public

canonicalHighbridgeBoundary : HighbridgeBoundary
canonicalHighbridgeBoundary = highbridge-boundary
  true false true true true true true false false true false false false

data JPMorganAcquisitionImpliesJPMorganPaidFee : Set where
data ConsultingFeeImpliesFundCapital : Set where
data GrossRedemptionImpliesProfit : Set where
data TransactionContextImpliesBankCommand : Set where
data FirstPersonClaimImpliesIndependentCausation : Set where
data LitigationAllegationImpliesAdjudicatedFact : Set where
data PostDealBCCImpliesDecisionAuthority : Set where
data UnsignedDraftImpliesCashRevenue : Set where

jpmorganAcquisitionDoesNotCreateFeePayer : JPMorganAcquisitionImpliesJPMorganPaidFee → ⊥
jpmorganAcquisitionDoesNotCreateFeePayer ()

consultingFeeDoesNotCreateFundCapital : ConsultingFeeImpliesFundCapital → ⊥
consultingFeeDoesNotCreateFundCapital ()

grossRedemptionDoesNotCreateProfit : GrossRedemptionImpliesProfit → ⊥
grossRedemptionDoesNotCreateProfit ()

transactionContextDoesNotCreateBankCommand : TransactionContextImpliesBankCommand → ⊥
transactionContextDoesNotCreateBankCommand ()

firstPersonClaimDoesNotCreateIndependentCausation : FirstPersonClaimImpliesIndependentCausation → ⊥
firstPersonClaimDoesNotCreateIndependentCausation ()

litigationAllegationDoesNotCreateAdjudicatedFact : LitigationAllegationImpliesAdjudicatedFact → ⊥
litigationAllegationDoesNotCreateAdjudicatedFact ()

postDealBCCDoesNotCreateDecisionAuthority : PostDealBCCImpliesDecisionAuthority → ⊥
postDealBCCDoesNotCreateDecisionAuthority ()

unsignedDraftDoesNotCreateCashRevenue : UnsignedDraftImpliesCashRevenue → ⊥
unsignedDraftDoesNotCreateCashRevenue ()

------------------------------------------------------------------------
-- Pareto acquisition after brokerage-source separation.
------------------------------------------------------------------------

data HighbridgeDebt : Set where
  transactionWorkProduct : HighbridgeDebt
  independentBrokerageCorroboration : HighbridgeDebt
  dubinSwiecaDecisionChain : HighbridgeDebt
  contemporaneousIntroductionCommunication : HighbridgeDebt
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
    "Recover the actual merger/acquisition advice, introductions, analyses or deliverables for which the exact USD15m invoice/wire was paid; invoice description plus Epstein testimony pay stated brokerage/advice, not work-product quality or exclusive causation."
  ∷ highbridge-acquisition independentBrokerageCorroboration 100 true
    "Corroborate Epstein's sworn introduction/financing account with Dubin, Staley, Swieca, JPMorgan deal-team testimony and contemporaneous records rather than treating his own deposition or USVI pleading as terminal truth."
  ∷ highbridge-acquisition dubinSwiecaDecisionChain 100 true
    "Resolve who at Dubin & Swieca/Highbridge approved the USD15m fee, why, how it was booked and any internal disagreement about its purpose."
  ∷ highbridge-acquisition contemporaneousIntroductionCommunication 99 true
    "Find the earliest calendar/email/phone or deal-team record joining Epstein, Dubin and Staley around the introduction and financing handoff."
  ∷ highbridge-acquisition jpmorganDealDocumentRole 99 true
    "Resolve Epstein/Financial Trust's exact role in Highbridge-JPMorgan transaction documents and distinguish adviser/broker references from decision authority."
  ∷ highbridge-acquisition consultingRetainerPerformance 98 true
    "Determine whether the unsigned 2005 USD2.25m retainer draft was executed in another copy and whether any USD450k installments were actually paid."
  ∷ highbridge-acquisition completeContributionHistory 97 true
    "Reconstruct each Epstein-controlled entity's Highbridge contributions, transfers and withdrawals from inception rather than deriving capital from the 2004 fee."
  ∷ highbridge-acquisition realisedReturnLedger 96 true
    "Compute realised Highbridge returns only after complete contribution/distribution/fee history; redemption proceeds alone are not gain."
  ∷ []
