module DASHI.Cognition.EpsteinFinancialTrustBearCrisisAwarenessSettlement20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- FINANCIAL TRUST / BEAR STEARNS CRISIS-AWARENESS AND SETTLEMENT BOUNDARY
------------------------------------------------------------------------

data CrisisSurface : Set where
  bearShareholding : CrisisSurface
  partialShareSale : CrisisSurface
  subprimeRepoConcernClaim : CrisisSurface
  seniorManagementAssuranceClaim : CrisisSurface
  mortgageStructuredExposure : CrisisSurface
  structuredCreditFundInvestment : CrisisSurface
  fundRollover : CrisisSurface
  inKindRecovery : CrisisSurface
  highGradeFundLossClaim : CrisisSurface
  settlement : CrisisSurface

record CrisisReceipt : Set where
  constructor crisis-receipt
  field
    label : String
    source : String
    boundedFinding : String
    surfaces : List CrisisSurface
    amountOrQuantity : Nat
    transactionFactPaid : Bool
    claimantAssertionPaid : Bool
    adjudicatedMeritsPaid : Bool
open CrisisReceipt public

bearSharesHeld : CrisisReceipt
bearSharesHeld = crisis-receipt
  "FTC Bear Stearns shareholding"
  "Financial Trust verified complaint, 3:09-cv-00106 / EFTA00722107 and DOJ court reproduction"
  "The verified complaint states Financial Trust held 120,000 Bear Stearns shares in a Merrill Lynch account and that Epstein had sole responsibility for FTC investment analysis and sale decisions concerning those shares."
  (bearShareholding ∷ []) 120000 true true false

august2007PartialSale : CrisisReceipt
august2007PartialSale = crisis-receipt
  "FTC August 2007 Bear share sale"
  "Financial Trust verified complaint / EFTA00730418"
  "The complaint states FTC sold 56,350 Bear shares on 6 August 2007 at approximately USD101.3799 per share after the Bear High-Grade/Enhanced fund problems, while retaining the remainder."
  (partialShareSale ∷ bearShareholding ∷ []) 56350 true true false

precrisisConcernClaim : CrisisReceipt
precrisisConcernClaim = crisis-receipt
  "Epstein/FTC claimed pre-crisis subprime and repo concern"
  "Financial Trust verified complaint paragraphs 23-29 / EFTA00730418"
  "FTC alleged that beginning in summer 2006 Epstein discussed Bear's mortgage exposure, subprime deterioration, repo-market access, liquidity and capital with senior Bear management and received repeated reassuring representations. This pays the claimant assertion, not the truth of each conversation or representation."
  (subprimeRepoConcernClaim ∷ seniorManagementAssuranceClaim ∷ mortgageStructuredExposure ∷ []) 0 false true false

record StructuredFundFlow : Set where
  constructor structured-fund-flow
  field
    investor : String
    fund : String
    date : String
    amountUSD : Nat
    source : String
    newCapitalContribution : Bool
    rolloverOrTransfer : Bool
    paid : Bool
open StructuredFundFlow public

ftcHG200401 : StructuredFundFlow
ftcHG200401 = structured-fund-flow
  "Financial Trust Company" "Bear Stearns High-Grade Structured Credit Strategies LP" "2004-01"
  15000000 "EFTA00597989 / EFTA01300739 settlement schedules" true false true

ftcEnhanced200608 : StructuredFundFlow
ftcEnhanced200608 = structured-fund-flow
  "Financial Trust Company" "Bear Stearns High-Grade Structured Credit Strategies Enhanced Leverage LP" "2006-08"
  20155344 "EFTA00597989 / EFTA01300739 settlement recitals/schedules"
  false true true

ftcABS200611 : StructuredFundFlow
ftcABS200611 = structured-fund-flow
  "Financial Trust Company" "Bear Stearns Asset Backed Securities Partners/Overseas" "2006-11"
  10000000 "EFTA00597989 / EFTA01300739 settlement schedules" true false true

couqABS200401 : StructuredFundFlow
couqABS200401 = structured-fund-flow
  "The C.O.U.Q. Foundation" "Bear Stearns Asset Backed Securities Partners/Overseas" "2004-01"
  10000000 "EFTA00597989 / EFTA01300739 settlement schedules" true false true

record StructuredCreditBoundary : Set where
  constructor structured-credit-boundary
  field
    ftcHGContributionPaid : Bool
    ftcEnhancedRolloverPaid : Bool
    ftcABSContributionPaid : Bool
    couqABSContributionPaid : Bool
    hg15mPlusEnhanced20155344AreIndependentSimultaneousPrincipal : Bool
    enhancedAmountReflectsHGWithdrawalRollover : Bool
    couqTransferredABSInterestBy2008 : Bool
    ftcReceivedABSInKindTrustInterestBy2009 : Bool
    exactRecoveryValuesPaid : Bool
open StructuredCreditBoundary public

canonicalStructuredCreditBoundary : StructuredCreditBoundary
canonicalStructuredCreditBoundary = structured-credit-boundary
  true true true true false true true true false

bearSettlement2011 : CrisisReceipt
bearSettlement2011 = crisis-receipt
  "Bear/FTC-COUQ-Epstein settlement"
  "EFTA00597963.. — 2011 settlement agreement and release"
  "Released settlement agreement provides USD9.2m from Bear/respondent parties to the claimants collectively in exchange for dismissal with prejudice and mutual releases. The agreement states respondents had no knowledge of how the payment would be allocated among claimants/counsel. Settlement does not adjudicate the underlying allegations."
  (settlement ∷ highGradeFundLossClaim ∷ []) 9200000 true false false

record CrisisAwarenessBoundary : Set where
  constructor crisis-awareness-boundary
  field
    ftcHeldBearSharesPaid : Bool
    partialSaleBeforeCollapsePaid : Bool
    claimantPrecrisisConcernAssertionPaid : Bool
    claimantSeniorManagementConversationAssertionPaid : Bool
    structuredCreditCapitalFlowsPaid : Bool
    settlementAmountPaid : Bool
    settlementAllocationToFTCPaid : Bool
    bearMisrepresentationAdjudicated : Bool
    precrisisConcernImpliesCrisisEngineering : Bool
    settlementImpliesAdmission : Bool
    lossClaimImpliesNetLossAfterSettlement : Bool
open CrisisAwarenessBoundary public

canonicalCrisisAwarenessBoundary : CrisisAwarenessBoundary
canonicalCrisisAwarenessBoundary = crisis-awareness-boundary
  true true true true true true false false false false false

data PrecrisisAwarenessImpliesEngineering : Set where
data SettlementImpliesAdmission : Set where
data ClaimedLossImpliesNetLoss : Set where
data SequentialRolloverImpliesDoublePrincipal : Set where

precrisisAwarenessDoesNotCreateEngineering : PrecrisisAwarenessImpliesEngineering → ⊥
precrisisAwarenessDoesNotCreateEngineering ()
settlementDoesNotCreateAdmission : SettlementImpliesAdmission → ⊥
settlementDoesNotCreateAdmission ()
claimedLossDoesNotCreateNetLoss : ClaimedLossImpliesNetLoss → ⊥
claimedLossDoesNotCreateNetLoss ()
sequentialRolloverDoesNotCreateDoublePrincipal : SequentialRolloverImpliesDoublePrincipal → ⊥
sequentialRolloverDoesNotCreateDoublePrincipal ()

data CrisisDebt : Set where
  bearTradeLedger : CrisisDebt
  structuredFundRecoveryLedger : CrisisDebt
  seniorManagementCallRecords : CrisisDebt
  settlementAllocation : CrisisDebt
  crisisLossTaxAccountingJoin : CrisisDebt
  complaintAllegationCorroboration : CrisisDebt

record CrisisAcquisition : Set where
  constructor crisis-acquisition
  field
    debt : CrisisDebt
    priority : Nat
    question : String
open CrisisAcquisition public

canonicalCrisisAcquisition : List CrisisAcquisition
canonicalCrisisAcquisition =
  crisis-acquisition bearTradeLedger 100
    "Acquire full Bear Stearns common-share purchase/sale/cost-basis ledger for FTC, including the 56,350-share August 2007 sale and remaining shares through collapse." ∷
  crisis-acquisition structuredFundRecoveryLedger 100
    "Resolve HG withdrawal proceeds into the USD20.155344m Enhanced rollover, ABS/Enhanced write-downs, COUQ's 2008 transfer, FTC's 2009 in-kind ABS Trust recovery and later cash/distributions. Do not double-count rolled HG capital." ∷
  crisis-acquisition seniorManagementCallRecords 99
    "Acquire contemporaneous call notes, emails or Bear-side records corroborating or contradicting the verified complaint's summer-2006-to-2008 liquidity/repo conversations." ∷
  crisis-acquisition settlementAllocation 99
    "Resolve how the USD9.2m settlement was allocated among FTC, COUQ, Epstein and counsel before using it in net-loss calculations." ∷
  crisis-acquisition crisisLossTaxAccountingJoin 98
    "Join Bear/structured-credit realised losses and settlement/recoveries to FTC's 2008-2012 negative investment-result accounting without assuming the entire annual loss arose from Bear." ∷
  crisis-acquisition complaintAllegationCorroboration 98
    "Compare each material Bear-liquidity/valuation allegation against contemporaneous SEC filings, call transcripts and respondent evidence; pleading status alone is not merits proof." ∷
  []
