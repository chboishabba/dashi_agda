module DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round7Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round6Exact as Prior
import DASHI.Cognition.EpsteinPalantirInvestmentInterest20261015Exact as Palantir
import DASHI.Cognition.EpsteinHoneycombPalantirOpportunityBridge20261015Exact as Honeycomb
import DASHI.Cognition.PalantirEarlyIntelligenceProductAcquisition20261015Exact as Early
import DASHI.Cognition.PalantirInstalledBaseProcurementPersistence20261015Exact as Persistence
import DASHI.Cognition.PalantirMissionExpansionContestability20261015Exact as Mission
import DASHI.Cognition.PalantirVoterDataAuthorityChain20261015Exact as Authority
import DASHI.Cognition.PalantirTIAStatutoryDispositionRefinement20261015Exact as TIA

------------------------------------------------------------------------
-- FINANCIAL / SYSTEMIC PARETO — ROUND 7, 2026-10-15
--
-- Direct Palantir investment evidence has advanced from generic interest to a
-- concrete secondary-market negotiation surface: Epstein asked Thiel about a
-- USD5.50/share block; Thiel discussed market range/timing; Epstein identified
-- the seller class as a mutual fund wanting out.  A separate Fiszel/Kahn route
-- later offered USD5/share access.  Execution/custody remains unpaid.
--
-- In parallel, the Palantir state-capacity lane now has bounded early-product,
-- procurement-persistence and mission-expansion receipts.  These raise research
-- priority without making Palantir=TIA, investment interest=ownership, or
-- repeated procurement=lock-in.
------------------------------------------------------------------------

data FinanceLane7 : Set where
  palantirSecondaryExecutionAndSellerIdentity : FinanceLane7
  palantirCustodyDisposition : FinanceLane7
  palantirEarlyCapitalRights : FinanceLane7
  palantirMissionExpansionExecution : FinanceLane7
  palantirInstalledBaseEconomics : FinanceLane7
  valarAndDefenseTechLookthrough : FinanceLane7
  priorFinanceFront : FinanceLane7

record FinanceProfile7 : Set where
  constructor finance-profile7
  field
    lane : FinanceLane7
    priority : Nat
    directReceiptPaid : Bool
    terminalEconomicObjectPaid : Bool
    sameObjectResidualHigh : Bool
    reading : String
open FinanceProfile7 public

canonicalFinanceFront7 : List FinanceProfile7
canonicalFinanceFront7 =
  finance-profile7 palantirSecondaryExecutionAndSellerIdentity 100 true false true
    "2014 investment advice, an October-2016 direct USD5.50/share secondary-block pricing discussion with Thiel and mutual-fund seller context, a December-2016 USD5/share Fiszel/Kahn opportunity, and 2018 company/IPO monitoring are paid. The highest-information residual is now exact seller/vehicle identity plus execution or explicit decline/expiry." ∷
  finance-profile7 palantirCustodyDisposition 100 true false true
    "Suggestive 2018 language ('hope you kept some stock') and continuing Palantir research are not custody evidence. Search brokerage/custody/cap-table/tax/estate records for a position; only after a holding is paid does disposition/IPO conversion become live." ∷
  finance-profile7 palantirEarlyCapitalRights 100 true false true
    "The historical In-Q-Tel amount/date and concrete CIA/NCTC/JIEDDO product-development objects are substantially paid at bounded source levels. The original security agreement and 2005 cap table remain the decisive capital/governance-rights object." ∷
  finance-profile7 palantirMissionExpansionExecution 100 true false true
    "The voter-data authority/processing chain and pending-ELITE-entry state are paid, as are litigation allegations about observer records in ICM. Actual ELITE ingestion, individual decision use, and same-subject propagation/remedy remain execution-level residuals rather than platform-capability inferences." ∷
  finance-profile7 palantirInstalledBaseEconomics 99 true false true
    "Repeated adoption, historical migration difficulty, a five-year USD1bn-ceiling DHS vehicle and concrete component calls pay a persistence mechanism. Interoperability initiatives and blocked procurement supply counterevidence. Full contract rights, migration costs, schema/configuration ownership and exact revenue remain the economic max-cut." ∷
  finance-profile7 valarAndDefenseTechLookthrough 99 true false true
    "Southern Trust's Valar II/III relationship is completed and valuable; a secondary lead points to an Anduril holding in a Valar III schedule, but no exact primary schedule row is promoted yet. Any Valar->Anduril bridge must remain fund-level indirect exposure, not Epstein operational control." ∷
  finance-profile7 priorFinanceFront 100 true true true
    "Wexner/Family Interest, Black/Apollo work-product implementation, Bear loss/recovery, Rothschild/Southern Trust, Valar realised returns/rights and modern private-capital housing-AI-power lanes remain co-frontier objects. Palantir does not displace them."
  ∷ []

record FinanceBoundary7 : Set where
  constructor finance-boundary7
  field
    pricingAdviceImpliesPurchase : Bool
    mutualFundSellerClassIdentifiesSeller : Bool
    twoSimilarOffersAreSameBlock : Bool
    stockPhraseImpliesCustody : Bool
    iqInvestmentImpliesCIAControl : Bool
    missionPlanningImpliesDeployment : Bool
    repeatedProcurementImpliesLockIn : Bool
    fundPortfolioHoldingImpliesLPDirectOwnership : Bool
open FinanceBoundary7 public

canonicalFinanceBoundary7 : FinanceBoundary7
canonicalFinanceBoundary7 = finance-boundary7
  false false false false false false false false

data PricingAdviceImpliesPurchase : Set where
data SimilarOffersImplySameBlock : Set where
data StockPhraseImpliesCustody : Set where
data FundHoldingImpliesLPDirectOwnership : Set where

pricingAdviceDoesNotCreatePurchase : PricingAdviceImpliesPurchase → ⊥
pricingAdviceDoesNotCreatePurchase ()

similarOffersDoNotCreateSameBlock : SimilarOffersImplySameBlock → ⊥
similarOffersDoNotCreateSameBlock ()

stockPhraseDoesNotCreateCustody : StockPhraseImpliesCustody → ⊥
stockPhraseDoesNotCreateCustody ()

fundHoldingDoesNotCreateLPDirectOwnership : FundHoldingImpliesLPDirectOwnership → ⊥
fundHoldingDoesNotCreateLPDirectOwnership ()

------------------------------------------------------------------------
-- Terminal public-acquisition cut for this round.
------------------------------------------------------------------------

data Debt7 : Set where
  october2016MutualFundSellerAndExecution : Debt7
  december2016FiszelSellerAndExecution : Debt7
  palantirCustodyPosition : Debt7
  originalIQTSecurityInstrument : Debt7
  eliteIngestionEndpoint : Debt7
  dhsBPADataMigrationTerms : Debt7
  valarIIIAndurilPrimarySchedule : Debt7

record Acquisition7 : Set where
  constructor acquisition7
  field
    debt : Debt7
    priority : Nat
    likelyPublicCorpusClosable : Bool
    instruction : String
open Acquisition7 public

canonicalAcquisition7 : List Acquisition7
canonicalAcquisition7 =
  acquisition7 october2016MutualFundSellerAndExecution 100 true
    "Resolve the mutual fund named or implied in EFTA02447787/02447940/02448060, the offered block/share class/quantity, transfer mechanism and whether Epstein accepted, countered, declined or let the offer expire." ∷
  acquisition7 december2016FiszelSellerAndExecution 100 true
    "Resolve who supplied Fiszel's USD5/share access, whether it was the same block as the October offer, and whether any Epstein-side entity executed or declined the opportunity." ∷
  acquisition7 palantirCustodyPosition 100 true
    "Search Southern Trust, HBRK, Financial Trust and estate/brokerage/tax position records for Palantir shares; suggestive correspondence does not substitute for a position object." ∷
  acquisition7 originalIQTSecurityInstrument 100 false
    "Acquire the 2005 In-Q-Tel investment/security agreement and Palantir cap table to pay security class, economic/governance/information rights and contractual customer-development access." ∷
  acquisition7 eliteIngestionEndpoint 100 true
    "Resolve the exact FOIA pending-Palantir-entry state to completed ingestion, rejection, cancellation or technical deferral and join any actual record to individual investigative use." ∷
  acquisition7 dhsBPADataMigrationTerms 99 true
    "Acquire full BPA/limited-source terms and predecessor vehicle chain, then quantify data/schema/configuration ownership, transition assistance, export rights, real migration attempts and vendor revenue." ∷
  acquisition7 valarIIIAndurilPrimarySchedule 99 true
    "Directly inspect the DOJ-hosted Valar III schedule row alleged to contain Anduril Series Seed before promoting indirect Southern Trust defense-tech exposure."
  ∷ []
