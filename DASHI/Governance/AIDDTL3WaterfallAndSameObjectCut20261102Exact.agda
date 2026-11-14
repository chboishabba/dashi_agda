module DASHI.Governance.AIDDTL3WaterfallAndSameObjectCut20261102Exact where

------------------------------------------------------------------------
-- ORIGINAL FILED CONTRACT / FINITE KNOWLEDGE NON-IDENTIFICATION WITNESS
--
-- CoreWeave Compute Acquisition Co. VII / V, Credit Agreement dated
-- 2025-07-28, SEC Exhibit 10.1 §2.20(b)(i)-(viii) pages 57-59:
-- https://www.sec.gov/Archives/edgar/data/1769628/000176962825000033/coreweave30-ex101xtermlo.htm
-- First Amendment dated 2025-12-31, SEC Exhibit 10.31 §§1.01,6.12:
-- https://www.sec.gov/Archives/edgar/data/1769628/000176962826000104/ex10311.htm
--
-- PRIOR repo owners NOT imported because separate OPEN PR #1101,
-- commit bbdab7b0464aeb0b9dc16b0666f5a2c8f6b1644b:
--  DASHI.Economics.AICoreWeaveOpenAIDDTL3CashHardwareWeld20261016Exact
--  DASHI.Economics.AICoreWeaveOpenAIContractRealisationCure20261016Exact
--  DASHI.Economics.AICoreWeaveSameObjectFinancingMaxCut20261016Exact
--  DASHI.Economics.AIOperatingCashTerminalDemandNonIdentification20261017Exact
-- The finite new synthetic witness is a narrower GOVERNANCE consumer
-- and does not inherit their proof ownership or conflate observed cash.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact as Atlas
import DASHI.Governance.AIContinuingCapitalFundingMaxCut20261102Exact as Funding

data ContractCashPriority : Set where
  firstEligibleOperatingExpense
    secondAgentFeesAndIndemnities
    thirdScheduledInterestAndSwaps
    fourthMinimumLiquidityTopup
    fifthScheduledPrincipalAndSwapTermination
    sixthContingentCashTrap
    seventhConditionalOtherOperatingAndCapitalExpenditure
    eighthDistributionReserve : ContractCashPriority

rank : ContractCashPriority → Nat
rank firstEligibleOperatingExpense = 1
rank secondAgentFeesAndIndemnities = 2
rank thirdScheduledInterestAndSwaps = 3
rank fourthMinimumLiquidityTopup = 4
rank fifthScheduledPrincipalAndSwapTermination = 5
rank sixthContingentCashTrap = 6
rank seventhConditionalOtherOperatingAndCapitalExpenditure = 7
rank eighthDistributionReserve = 8

interestPrecedesPrincipal :
  rank thirdScheduledInterestAndSwaps ≡ 3
interestPrecedesPrincipal = refl

principalPrecedesReserve :
  rank fifthScheduledPrincipalAndSwapTermination + 3
  ≡ rank eighthDistributionReserve
principalPrecedesReserve = refl

-- The contract explicitly caps expense reimbursements in the first priority
-- to USD50m within a calendar month; this is NOT a bound on all expenses.
firstStepMonthlyOperatingExpenseCapMillionUSD : Nat
firstStepMonthlyOperatingExpenseCapMillionUSD = 50

firstStepCapExactlyFifty :
  firstStepMonthlyOperatingExpenseCapMillionUSD ≡ 50
firstStepCapExactlyFifty = refl

data ReleaseCondition : Set where
  conditionalReserveWithdrawalNotDemonstrated
    reserveWithdrawalConditionsSatisfied : ReleaseCondition

data FinancedCashOrigin : Set where
  cashFromIndependentCustomer
    cashFromParentOrUnobservedSource : FinancedCashOrigin

-- **SYNTHETIC NONIDENTIFICATION**, not a numerical reconstruction of a
-- real DDTL3 monthly ratio or actual distribution. The same 85/100 filed-
-- style CRR and USD85m Available Cash balance can arise under two source
-- compositions; the released documents do not give the realised balances.
data SyntheticCashWorld : Set where
  billedAndIndependentCash
    partlyBilledAndEquityCure : SyntheticCashWorld

record AggregateContractView : Set where
  constructor aggregateContractView
  field
    modelledAvailableCashMillionUSD : Nat
    modelledCRRBasisPoints : Nat
open AggregateContractView public

observedView : SyntheticCashWorld → AggregateContractView
observedView _ = aggregateContractView 85 8500

actualCashOrigin : SyntheticCashWorld → FinancedCashOrigin
actualCashOrigin billedAndIndependentCash = cashFromIndependentCustomer
actualCashOrigin partlyBilledAndEquityCure = cashFromParentOrUnobservedSource

sameAggregateView :
  observedView billedAndIndependentCash
  ≡ observedView partlyBilledAndEquityCure
sameAggregateView = refl

differentExternalCashComposition :
  actualCashOrigin billedAndIndependentCash
  ≡ actualCashOrigin partlyBilledAndEquityCure → ⊥
differentExternalCashComposition ()

cashAndCRRCollision :
  NF.NonFactorabilityWitness observedView actualCashOrigin
cashAndCRRCollision =
  NF.nonFactorabilityWitness
    billedAndIndependentCash partlyBilledAndEquityCure
    sameAggregateView differentExternalCashComposition

sameAccountAndRatioCannotDetermineTerminalCash :
  NF.FactorsThrough observedView actualCashOrigin → ⊥
sameAccountAndRatioCannotDetermineTerminalCash =
  NF.witnessRulesOutEveryFlatFactorisation cashAndCRRCollision

-- This synthetic distinction is *stronger than* simply asserting
-- that a ratio could receive equity-cure credit: actual billed amounts
-- need not have settled, and cash in the collateral account may include
-- parent/other deposits and transfers. Both are allowed by the filings.
data CRRCompliantImpliesNamedCustomerCash : Set where
crrComplianceDoesNotProveCustomerSettlement :
  CRRCompliantImpliesNamedCustomerCash → ⊥
crrComplianceDoesNotProveCustomerSettlement ()

data AccountBalanceImpliesCompanyDistribution : Set where
cashBalanceDoesNotProveDistributableDividend :
  AccountBalanceImpliesCompanyDistribution → ⊥
cashBalanceDoesNotProveDistributableDividend ()

data ExactLegalWaterfallImpliesObservedPayment : Set where
waterfallRuleDoesNotSupplyAccountStatement :
  ExactLegalWaterfallImpliesObservedPayment → ⊥
waterfallRuleDoesNotSupplyAccountStatement ()

reusedFutureBuildFinancingBoundary :
  NF.FactorsThrough Funding.currentMaturityView
    Funding.continuationView → ⊥
reusedFutureBuildFinancingBoundary =
  Funding.currentMaturityCannotDetermineFutureBuild

originalWaterfall : Atlas.SourceReceipt
originalWaterfall = Atlas.coreWeaveDDTL3Sec220WaterfallOriginal

originalCure : Atlas.SourceReceipt
originalCure = Atlas.coreWeaveDDTL3CureDecember31Original

record CompleteSameObjectProjectPaymentReceipt : Set where
  constructor completeSameObjectProjectPaymentReceipt
  field
    lenderAccountStatementAndDate : String
    actualCustomerInvoiceAndCashSettlement : String
    anyParentDepositAndEquityCureSeparate : String
    feeInterestPrincipalReserveActualAmounts : String
    liquidityAndCashTrapTriggerActualOutcome : String
    otherOpExConditionAndExpenditure : String
    reserveWithdrawalAndActualDistribution : String
    contractAndGpuSerialToCapacityBridge : String
    refinancingIssuanceAndFinalCreditorRisk : String

contractLegalBoundary : String
contractLegalBoundary =
  "Source-written agreement ranks a conditional legal payment priority; does not reveal realised ledger. Amended CRR uses actual amounts billed or received without duplication plus equity cure; billed is not settled cash, and covenant compliance is not observed. Actual parent or outside deposits can enter account. Prior repo PR #1101 owns the DDTL3 source reconstruction; this branch only provides conditional governance/independent-cash consumer non-identification."
