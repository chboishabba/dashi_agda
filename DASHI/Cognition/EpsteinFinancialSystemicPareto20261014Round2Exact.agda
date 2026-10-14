module DASHI.Cognition.EpsteinFinancialSystemicPareto20261014Round2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialTrustAnnualStatementSpine20261014Exact as Annual
import DASHI.Cognition.EpsteinFinancialTrustFeePayerAtlas20261014Exact as Fees
import DASHI.Cognition.EpsteinFinancialTrustPre2013CapitalAtlas20261014Exact as FTC
import DASHI.Cognition.EpsteinFamilyInterestWexnerCapitalBridge20261014Exact as FamilyInterest
import DASHI.Cognition.EpsteinSouthernTrustCapitalizationClosure20261014Exact as STCapital
import DASHI.Cognition.EpsteinSouthernTrustInvestmentFlowAtlas20261014Exact as STFlow
import DASHI.Cognition.EpsteinBlackApolloTrustStructure20261014Exact as BlackApollo
import DASHI.Cognition.EpsteinRothschildSouthernTrustServiceReceiptRound20261014Exact as Rothschild
import DASHI.Cognition.EpsteinValarLPMechanics20261014Exact as ValarTerms
import DASHI.Cognition.EpsteinValarPortfolioLookthrough20261014Exact as ValarPortfolio
import DASHI.Cognition.EpsteinFinancialTrustBearCrisisAwarenessSettlement20261014Exact as BearCrisis
import DASHI.Cognition.EpsteinLiquidFundingOwnershipWinddownReceipt20261014Exact as Liquid
import DASHI.Cognition.EpsteinUSVIEDCTaxIncidence20261014Exact as EDC
import DASHI.Cognition.PrivateCapitalHousingAIInfrastructureCrossPollinationExact as ModernCapital

------------------------------------------------------------------------
-- FINANCIAL / SYSTEMIC PARETO — ROUND 2, 2026-10-14
--
-- This round follows the source acquisition completed after the earlier global
-- Pareto.  Broad existence questions have fallen off the frontier:
--   * FTC primary annual statements are paid continuously 1999-2012;
--   * Southern Trust 2013-17 fee/net-sales line reconciles to identified payer
--     streams within scope;
--   * Valar II/III LP commitments and generic fund economics are paid;
--   * fungible-capital capacity replaces unnecessary dollar-by-dollar tracing;
--   * Liquid Funding participation/wind-down and FTC/Bear litigation are paid
--     at bounded source-local levels.
------------------------------------------------------------------------

data FinanceLane : Set where
  financialTrustFeePayerAndCapitalArchitecture : FinanceLane
  familyInterestWexnerPartnershipEconomics : FinanceLane
  southernTrustFungibleCapitalDeployment : FinanceLane
  blackApolloDerivedTrustTransactions : FinanceLane
  bearStructuredCreditCrisisEconomics : FinanceLane
  valarThielLPPortfolioEconomics : FinanceLane
  rothschildAdviceCapitalAndAlgorithms : FinanceLane
  usviTaxRetainedCapitalIncidence : FinanceLane
  liquidFundingStructuredFinanceWinddown : FinanceLane
  privateCapitalHousingAIAssetisation : FinanceLane

record FinanceProfile : Set where
  constructor finance-profile
  field
    lane : FinanceLane
    priority : Nat
    directReceiptsHigh : Bool
    sameObjectResidualHigh : Bool
    secondOrderLeverageHigh : Bool
    thirdOrderLeverageHigh : Bool
    beneficiaryIncidenceDebtHigh : Bool
    reading : String
open FinanceProfile public

canonicalFinanceFront : List FinanceProfile
canonicalFinanceFront =
  finance-profile financialTrustFeePayerAndCapitalArchitecture 100 true true true true true
    "FTC's 1999-2012 primary annual accounting spine is closed, including signed crisis-loss years. USD377.743m fee income across 2000-06 and USD5.166m across 2007-12 are accounting facts, but payer allocation remains largely open. Highbridge's USD15m 2004 M&A fee is the first same-object payer anchor; Wexner chronology/revenue collapse is a strong acquisition signal, not sole-payer proof."
  ∷ finance-profile familyInterestWexnerPartnershipEconomics 100 true true true true true
    "JPM records FTC as GP of Family Interest LP with a Wexner children's trust LP, and a 2003 USD55.878m Family Interests capital movement is paid. Partnership agreement, capital accounts, GP fees/authority and partner economics remain the key same-object residuals; GP status is not beneficial ownership of LP capital."
  ∷ finance-profile southernTrustFungibleCapitalDeployment 100 true true true true true
    "Southern Trust's 2013-17 net-sales line reconciles within scope to Black, Rothschild and Sinofsky payment streams. Paid inflows increase a fungible capital pool; Valar/Honeycomb/other deployments are paid separately. Earmarking is not required for the balance-sheet capacity claim and is not inferred."
  ∷ finance-profile blackApolloDerivedTrustTransactions 100 true true true true true
    "Epstein's Black trust/tax work directly touched Apollo-derived partnership/management wealth, and an Epstein entity also held Apollo public equity. The live cut is transaction mechanics, trust consideration, accepted/rejected advice and payment-to-work-product joins, not an unsupported Apollo-corporate-retention theorem."
  ∷ finance-profile bearStructuredCreditCrisisEconomics 100 true true true true true
    "FTC was a large Bear/structured-finance investor, alleged pre-crisis subprime/repo awareness from 2006, sold part of its Bear share position in August 2007, later litigated/arbitrated Bear-related claims and entered a USD9.2m collective settlement. Trade/fund ledgers and loss/recovery allocation now dominate; claimant allegations remain distinct from adjudicated merits."
  ∷ finance-profile valarThielLPPortfolioEconomics 99 true true true true true
    "Southern Trust's USD40m Valar II/III commitments, paid-in capital, generic fee/carry mechanics, Thiel economic/veto rights and Fund II portfolio exposure are paid. Side letters, distributions, Fund III portfolio and estate disposition are the high-value residuals; LP exposure does not create portfolio-company control."
  ∷ finance-profile rothschildAdviceCapitalAndAlgorithms 99 true true true true true
    "Released 2015 agreements/invoice/wires pay a Rothschild-Southern Trust consulting/payment relationship spanning risk analysis, estate planning, strategic matters, algorithms and US-matter language. Exact agreement-version settlement, delivered work product and government-intervention chain remain open."
  ∷ finance-profile usviTaxRetainedCapitalIncidence 99 true true true true true
    "Court-filed analysis pays roughly USD219.8m FTC and USD80.6m Southern Trust EDC benefit, while primary compliance reports pay employment/local-spend/capital conditions and some compliance failures. The live question is quantitative public/private incidence, not automatic corruption inference."
  ∷ finance-profile liquidFundingStructuredFinanceWinddown 99 true true true true true
    "Bear's approximately 40% Liquid Funding interest, Bear investment-management role, FTC Class A voting-unit interest, repo/mortgage plumbing and 2008 wind-down are paid. Exact cap table and liability-payoff source remain open; rescue chronology does not pay a Federal Reserve bailout attribution."
  ∷ finance-profile privateCapitalHousingAIAssetisation 99 true true true true true
    "Current Apollo/Blackstone/BlackRock/KKR/Brookfield-style capital transforms housing, compute, data-centres and power into recurring-cashflow institutional assets. This is a contemporary structural cross-pollination around the historically direct Black/Apollo lane, not evidence that Epstein controlled modern private-capital strategy."
  ∷ []

record Round2Boundary : Set where
  constructor round2-boundary
  field
    capitalPoolContributionRequiresEarmarking : Bool
    capitalPoolContributionImpliesPayerControlledDeployment : Bool
    gpStatusImpliesLPBeneficialOwnership : Bool
    lpStatusImpliesPortfolioCompanyControl : Bool
    accountingViewDifferenceImpliesFraud : Bool
    annualRevenueImpliesNamedClient : Bool
    revenueCollapseImpliesSolePayer : Bool
    taxBenefitImpliesImproperOfficialAct : Bool
    liquidFundingWinddownImpliesFedBailout : Bool
    precrisisAwarenessImpliesCrisisEngineering : Bool
    settlementImpliesAdmission : Bool
    historicalEpsteinBlackRelationshipImpliesModernApolloStrategy : Bool
    sameManagerAcrossHousingAIImpliesCommonPoliticalCommand : Bool
    sourceTypedCapitalInfrastructureWorthInvestigating : Bool
open Round2Boundary public

canonicalRound2Boundary : Round2Boundary
canonicalRound2Boundary = round2-boundary
  false false false false false false false false false false false false false true

data CapitalContributionImpliesEarmarking : Set where
data GPImpliesBeneficialOwnership : Set where
data LPImpliesPortfolioControl : Set where
data AccountingDifferenceImpliesFraud : Set where
data RevenueImpliesNamedClient : Set where
data RevenueCollapseImpliesSolePayer : Set where
data TaxBenefitImpliesImproperAct : Set where
data WinddownImpliesFedBailout : Set where
data AwarenessImpliesEngineering : Set where
data SettlementImpliesAdmission : Set where
data HistoricalRelationshipImpliesModernStrategy : Set where
data SameManagerImpliesCommonCommand : Set where

capitalContributionDoesNotCreateEarmarking : CapitalContributionImpliesEarmarking → ⊥
capitalContributionDoesNotCreateEarmarking ()

gpDoesNotCreateBeneficialOwnership : GPImpliesBeneficialOwnership → ⊥
gpDoesNotCreateBeneficialOwnership ()

lpDoesNotCreatePortfolioControl : LPImpliesPortfolioControl → ⊥
lpDoesNotCreatePortfolioControl ()

accountingDifferenceDoesNotCreateFraud : AccountingDifferenceImpliesFraud → ⊥
accountingDifferenceDoesNotCreateFraud ()

revenueDoesNotCreateNamedClient : RevenueImpliesNamedClient → ⊥
revenueDoesNotCreateNamedClient ()

revenueCollapseDoesNotCreateSolePayer : RevenueCollapseImpliesSolePayer → ⊥
revenueCollapseDoesNotCreateSolePayer ()

taxBenefitDoesNotCreateImproperAct : TaxBenefitImpliesImproperAct → ⊥
taxBenefitDoesNotCreateImproperAct ()

winddownDoesNotCreateFedBailout : WinddownImpliesFedBailout → ⊥
winddownDoesNotCreateFedBailout ()

awarenessDoesNotCreateEngineering : AwarenessImpliesEngineering → ⊥
awarenessDoesNotCreateEngineering ()

settlementDoesNotCreateAdmission : SettlementImpliesAdmission → ⊥
settlementDoesNotCreateAdmission ()

historicalRelationshipDoesNotCreateModernStrategy : HistoricalRelationshipImpliesModernStrategy → ⊥
historicalRelationshipDoesNotCreateModernStrategy ()

sameManagerDoesNotCreateCommonCommand : SameManagerImpliesCommonCommand → ⊥
sameManagerDoesNotCreateCommonCommand ()

------------------------------------------------------------------------
-- Remaining global acquisition order after this round.
------------------------------------------------------------------------

data Round2Debt : Set where
  wexnerFamilyInterestFeeAndCapitalLedger : Round2Debt
  bearAndHighGradeLossRecoveryLedger : Round2Debt
  blackApolloTrustWorkProductJoin : Round2Debt
  valarSideLettersDistributionsPortfolioIII : Round2Debt
  rothschildWorkProductSettlementJoin : Round2Debt
  liquidFundingCapTableAndPayoff : Round2Debt
  edcPublicPrivateIncidence : Round2Debt
  modernSameFundHousingAIInfrastructureLookthrough : Round2Debt

record Round2Acquisition : Set where
  constructor round2-acquisition
  field
    debt : Round2Debt
    priority : Nat
    likelyPublicWebClosable : Bool
    instruction : String
open Round2Acquisition public

canonicalRound2Acquisition : List Round2Acquisition
canonicalRound2Acquisition =
  round2-acquisition wexnerFamilyInterestFeeAndCapitalLedger 100 false
    "Acquire Wexner/Family Interest invoices, bank credits, partnership agreement and capital accounts. Do not promote the fee-income collapse into sole-payer proof without those records." ∷
  round2-acquisition bearAndHighGradeLossRecoveryLedger 100 true
    "Resolve FTC/COUQ Bear common-stock and High-Grade/Enhanced-fund cost basis, sales/redemptions, write-downs and settlement allocation, then join to 2008-12 annual loss accounting." ∷
  round2-acquisition blackApolloTrustWorkProductJoin 100 true
    "Acquire Epstein-authored trust/tax work products, exact Apollo-derived asset schedules and implementation records, and join Black payment tranches to individual work objects." ∷
  round2-acquisition valarSideLettersDistributionsPortfolioIII 99 true
    "Resolve Southern Trust-specific Valar terms, Fund III portfolio, distributions/fees and estate disposition; generic PPM terms are already paid." ∷
  round2-acquisition rothschildWorkProductSettlementJoin 99 true
    "Resolve exact Rothschild agreement/version/payment joins and delivered algorithm/risk/estate work product, preserving advice versus government decision authority." ∷
  round2-acquisition liquidFundingCapTableAndPayoff 99 false
    "Recover exact Liquid Funding Holdings cap table and March-April 2008 payoff ledger/source. Rescue timing alone remains insufficient." ∷
  round2-acquisition edcPublicPrivateIncidence 98 true
    "Quantify payroll, local procurement/capital, taxes paid, tax benefit and later repayments to compare local public benefit with retained private capital." ∷
  round2-acquisition modernSameFundHousingAIInfrastructureLookthrough 98 true
    "Resolve same-fund/vehicle exposure across housing, AI compute, data-centres and power for large managers; same manager name alone is not same capital pool or common strategy." ∷
  []
