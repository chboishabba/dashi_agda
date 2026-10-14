module DASHI.Cognition.EpsteinSouthernTrustCapitalizationClosure20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinSouthernTrustInvestmentFlowAtlas20261014Exact as Flow
import DASHI.Cognition.EpsteinBlackRothschildTransactionAtlas20261014Exact as Tx
import DASHI.Cognition.EpsteinRothschildSouthernTrustServiceReceiptRound20261014Exact as Rothschild

------------------------------------------------------------------------
-- SOUTHERN TRUST CAPITALIZATION CLOSURE
--
-- Court-filed expert material gives the annual Southern Trust net-sales line.
-- Independently identified Black, Rothschild and Sinofsky payments reconcile
-- those net-sales totals exactly for 2013-2017.  This is a bounded accounting
-- closure for the fee-income line, not a complete ledger of every asset,
-- liability, loan, transfer or other Epstein entity.
------------------------------------------------------------------------

record AnnualRevenue : Set where
  constructor annual-revenue
  field
    year : Nat
    netSalesUSD : Nat
    source : String
open AnnualRevenue public

southernTrustAnnualRevenue : List AnnualRevenue
southernTrustAnnualRevenue =
  annual-revenue 2013 51000000 "USVI v JPMorgan, Doc 290-7, expert exhibit based on Southern Trust financial/tax records" ∷
  annual-revenue 2014 70000000 "USVI v JPMorgan, Doc 290-7" ∷
  annual-revenue 2015 54999980 "USVI v JPMorgan, Doc 290-7" ∷
  annual-revenue 2016 0 "USVI v JPMorgan, Doc 290-7" ∷
  annual-revenue 2017 8000000 "USVI v JPMorgan, Doc 290-7" ∷
  []

record IdentifiedFeeSource : Set where
  constructor identified-fee-source
  field
    payer : String
    amountUSD : Nat
    paymentEvidence : String
    purposeClass : String
    exactAnnualReconciliationPaid : Bool
    wrongdoingPaid : Bool
open IdentifiedFeeSource public

blackFeeSource : IdentifiedFeeSource
blackFeeSource = identified-fee-source
  "Leon Black / Black family payment stream"
  158000000
  "Dechert 2021 report plus transaction/invoice records"
  "trust/estate/tax/family-office and related advisory services as attributed by Dechert; individual wires remain separately scoped where possible"
  true false

rothschildFeeSource : IdentifiedFeeSource
rothschildFeeSource = identified-fee-source
  "Edmond de Rothschild / Benjamin de Rothschild payment stream"
  24999980
  "December 2015 Deutsche Bank wires plus released Southern Trust/Rothschild agreements and invoice context"
  "risk analysis / algorithms / strategic-business / estate-planning / US-matters contractual context; exact wire-to-version join partly open"
  true false

sinofskyFeeSource : IdentifiedFeeSource
sinofskyFeeSource = identified-fee-source
  "Steven Sinofsky"
  1000000
  "EFTA00675845 / EFTA01500125 and related correspondence"
  "advisory fee concerning Microsoft separation/negotiation and related advice"
  true false

record CapitalizationClosure : Set where
  constructor capitalization-closure
  field
    netSales2013to2017USD : Nat
    identifiedBlackUSD : Nat
    identifiedRothschildUSD : Nat
    identifiedSinofskyUSD : Nat
    identifiedCombinedUSD : Nat
    identifiedSourcesReconcileNetSales : Bool
    feeIncomeLineFullyAllocatedWithinScope : Bool
    allSouthernTrustCashFlowsKnown : Bool
    allEpsteinEntityCashFlowsKnown : Bool
open CapitalizationClosure public

canonicalCapitalizationClosure : CapitalizationClosure
canonicalCapitalizationClosure = capitalization-closure
  183999980 158000000 24999980 1000000 183999980 true true false false

record FungibleCapacityBridge : Set where
  constructor fungible-capacity-bridge
  field
    identifiedFeesCapitaliseSouthernTrust : Bool
    capitalPoolCanFundLaterInvestments : Bool
    exactDollarEarmarkingRequiredForCapacityClaim : Bool
    exactDollarEarmarkingRequiredForPayerSpecificFundingClaim : Bool
    inflowPayerControlsInvestmentSelection : Bool
open FungibleCapacityBridge public

canonicalFungibleCapacityBridge : FungibleCapacityBridge
canonicalFungibleCapacityBridge = fungible-capacity-bridge
  true true false true false

data FeeContributionImpliesEarmarkedInvestment : Set where
data FeePayerImpliesInvestmentControl : Set where
data RevenueClosureImpliesCompleteEntityLedger : Set where

feeContributionDoesNotCreateEarmarking : FeeContributionImpliesEarmarkedInvestment → ⊥
feeContributionDoesNotCreateEarmarking ()

feePayerDoesNotCreateInvestmentControl : FeePayerImpliesInvestmentControl → ⊥
feePayerDoesNotCreateInvestmentControl ()

revenueClosureDoesNotCreateCompleteEntityLedger : RevenueClosureImpliesCompleteEntityLedger → ⊥
revenueClosureDoesNotCreateCompleteEntityLedger ()

------------------------------------------------------------------------
-- Remaining capitalization questions are narrower.
------------------------------------------------------------------------

data CapitalizationDebt : Set where
  pre2013FinancialTrustClientAllocation : CapitalizationDebt
  nonFeeInflowsAndLoans : CapitalizationDebt
  interEntityTransfers : CapitalizationDebt
  taxesAndEDCBenefitIncidence : CapitalizationDebt
  investmentDeploymentTiming : CapitalizationDebt

record CapitalizationAcquisition : Set where
  constructor capitalization-acquisition
  field
    debt : CapitalizationDebt
    priority : Nat
    question : String
open CapitalizationAcquisition public

canonicalCapitalizationAcquisition : List CapitalizationAcquisition
canonicalCapitalizationAcquisition =
  capitalization-acquisition pre2013FinancialTrustClientAllocation 100
    "Resolve Financial Trust Company's earlier aggregated client/fee income and identify payer-level sources without projecting Southern Trust's later completeness backwards."
  ∷ capitalization-acquisition investmentDeploymentTiming 99
    "Join Southern Trust's annual capitalization to capital calls, investments and distributions to measure deployment intensity and retained liquidity."
  ∷ capitalization-acquisition interEntityTransfers 98
    "Map Southern Trust/Southern Financial/Financial Trust/Gratitude America and other Epstein-entity transfers without double counting the same economic capital."
  ∷ capitalization-acquisition nonFeeInflowsAndLoans 97
    "Separate advisory fee revenue from loans, asset-sale proceeds, investment redemptions and other non-fee receipts."
  ∷ capitalization-acquisition taxesAndEDCBenefitIncidence 96
    "Quantify taxes, USVI EDC benefits and retained after-tax capital using the court-filed expert schedules without treating tax incentives as proof of misconduct."
  ∷ []
