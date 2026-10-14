module DASHI.Cognition.EpsteinSouthernTrustInvestmentFlowAtlas20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBlackRothschildTransactionAtlas20261014Exact as Inflow

------------------------------------------------------------------------
-- SOUTHERN TRUST / SOUTHERN FINANCIAL DOWNSTREAM INVESTMENT-FLOW ATLAS
--
-- Source spine: Deutsche Bank production charts reproduced in DOJ/FBI EFTA
-- materials (EFTA00080250..252 / duplicate lineage including EFTA00027019).
--
-- Critical non-collapse rule: entity-level inflow and later entity-level
-- outflow do not establish source-specific tracing through a fungible account.
-- This file pays the entity->fund transactions and aggregate fund totals only.
------------------------------------------------------------------------

data InvestmentEntity : Set where
  southernTrust : InvestmentEntity
  southernFinancial : InvestmentEntity
  valarGlobalII : InvestmentEntity
  valarGlobalIII : InvestmentEntity
  honeycombPartners : InvestmentEntity
  honeycombVenturesI : InvestmentEntity
  boothbayMultiStrategy : InvestmentEntity
  boothbayAbsoluteStrategies : InvestmentEntity
  coatueEnterprises : InvestmentEntity
  neoteny3 : InvestmentEntity
  joichiIto : InvestmentEntity

record FundFlow : Set where
  constructor fund-flow
  field
    date : String
    payer : InvestmentEntity
    recipient : InvestmentEntity
    amountUSD : Nat
    bates : String
    paid : Bool
open FundFlow public

valarIIFlows : List FundFlow
valarIIFlows =
  fund-flow "2015-01-21" southernTrust valarGlobalII 150000 "DB-SDNY-0004346" true
  ∷ fund-flow "2015-02-12" southernTrust valarGlobalII 900000 "DB-SDNY-0004412" true
  ∷ fund-flow "2015-03-30" southernTrust valarGlobalII 2700000 "DB-SDNY-00045xx" true
  ∷ fund-flow "2015-07-24" southernTrust valarGlobalII 600000 "DB-SDNY-0004790" true
  ∷ fund-flow "2015-09-24" southernTrust valarGlobalII 1950000 "DB-SDNY-000492x" true
  ∷ []

valarIIIFlows : List FundFlow
valarIIIFlows =
  fund-flow "2016-06-23" southernTrust valarGlobalIII 250000 "DB-SDNY-0005526" true
  ∷ fund-flow "2016-08-18" southernTrust valarGlobalIII 1250000 "DB-SDNY-0005667" true
  ∷ fund-flow "2016-12-12" southernTrust valarGlobalIII 3750000 "DB-SDNY-0005932" true
  ∷ fund-flow "2017-04-20" southernTrust valarGlobalIII 3000000 "DB-SDNY-0006240" true
  ∷ fund-flow "2017-07-24" southernTrust valarGlobalIII 4250000 "DB-SDNY-0006407" true
  ∷ fund-flow "2017-10-11" southernTrust valarGlobalIII 2250000 "DB-SDNY-0006652" true
  ∷ fund-flow "2018-01-05" southernTrust valarGlobalIII 1500000 "DB-SDNY-0006901" true
  ∷ fund-flow "2018-01-15" southernTrust valarGlobalIII 500000 "DB-SDNY-0006985" true
  ∷ fund-flow "2018-06-01" southernTrust valarGlobalIII 1750000 "DB-SDNY-0007348" true
  ∷ fund-flow "2019-01-08" southernTrust valarGlobalIII 2500000 "DB-SDNY-0007987" true
  ∷ fund-flow "2019-04-17" southernTrust valarGlobalIII 1500000 "DB-SDNY-0008222" true
  ∷ []

record ValarAggregate : Set where
  constructor valar-aggregate
  field
    fundIIUSD : Nat
    fundIIIUSD : Nat
    combinedUSD : Nat
    source : String
    exactEntityToFundPaymentsPaid : Bool
    sourceSpecificInflowTracingPaid : Bool
open ValarAggregate public

canonicalValarAggregate : ValarAggregate
canonicalValarAggregate = valar-aggregate
  6300000 22500000 28800000
  "Deutsche Bank transaction charts in EFTA00080250..252; arithmetic sum of listed Southern Trust -> Valar II/III rows"
  true false

honeycombFlows : List FundFlow
honeycombFlows =
  fund-flow "2016-05-31" southernTrust honeycombPartners 20000000 "DB-SDNY-0005457" true
  ∷ fund-flow "2017-07-10" southernTrust honeycombVenturesI 1000000 "DB-SDNY-0006407" true
  ∷ fund-flow "2018-06-27" southernTrust honeycombPartners 10000000 "DB-SDNY-0007348" true
  ∷ fund-flow "2018-06-28" southernTrust honeycombPartners 5000000 "DB-SDNY-0007348" true
  ∷ fund-flow "2018-09-28" southernTrust honeycombPartners 8000000 "DB-SDNY-0007623" true
  ∷ fund-flow "2019-03-28" southernTrust honeycombPartners 10000000 "DB-SDNY-0008154" true
  ∷ []

record HoneycombAggregate : Set where
  constructor honeycomb-aggregate
  field
    partnersUSD : Nat
    venturesIUSD : Nat
    combinedLocatedUSD : Nat
open HoneycombAggregate public

canonicalHoneycombAggregate : HoneycombAggregate
canonicalHoneycombAggregate = honeycomb-aggregate 53000000 1000000 54000000

boothbayFlows : List FundFlow
boothbayFlows =
  fund-flow "2014-05-02" southernFinancial boothbayMultiStrategy 10000000 "DB-SDNY-0003845" true
  ∷ fund-flow "2015-06-30" southernFinancial boothbayAbsoluteStrategies 2000000 "DB-SDNY-0004675" true
  ∷ fund-flow "2015-07-28" southernFinancial boothbayAbsoluteStrategies 7000000 "DB-SDNY-0004745" true
  ∷ fund-flow "2015-09-28" southernFinancial boothbayAbsoluteStrategies 4250000 "DB-SDNY-0004881" true
  ∷ fund-flow "2016-03-01" southernFinancial boothbayAbsoluteStrategies 10000000 "DB-SDNY-0005280" true
  ∷ fund-flow "2016-03-31" southernFinancial boothbayAbsoluteStrategies 5000000 "DB-SDNY-0005281" true
  ∷ []

record BoothbayAggregate : Set where
  constructor boothbay-aggregate
  field
    locatedUSD : Nat
open BoothbayAggregate public

canonicalBoothbayAggregate : BoothbayAggregate
canonicalBoothbayAggregate = boothbay-aggregate 38250000

------------------------------------------------------------------------
-- Exact cross-pollination significance.
------------------------------------------------------------------------

record SouthernTrustFlowBoundary : Set where
  constructor southern-trust-flow-boundary
  field
    blackInflowReceiptsExist : Bool
    rothschildInflowReceiptsExist : Bool
    valarOutflowReceiptsExist : Bool
    sameEntityTemporalPathExists : Bool
    blackSpecificDollarsToValarPaid : Bool
    rothschildSpecificDollarsToValarPaid : Bool
    temporalAdjacencyCreatesSourceTracing : Bool
    commonRecipientCreatesCommonPurpose : Bool
open SouthernTrustFlowBoundary public

canonicalSouthernTrustFlowBoundary : SouthernTrustFlowBoundary
canonicalSouthernTrustFlowBoundary = southern-trust-flow-boundary
  true true true true false false false false

data FungibleAccountPathImpliesSourceSpecificFunding : Set where
data CommonRecipientImpliesCommonPurpose : Set where
data FundInvestmentImpliesOperationalControl : Set where

temporalAccountPathDoesNotCreateSourceTracing : FungibleAccountPathImpliesSourceSpecificFunding → ⊥
temporalAccountPathDoesNotCreateSourceTracing ()

commonRecipientDoesNotCreateCommonPurpose : CommonRecipientImpliesCommonPurpose → ⊥
commonRecipientDoesNotCreateCommonPurpose ()

fundInvestmentDoesNotCreateOperationalControl : FundInvestmentImpliesOperationalControl → ⊥
fundInvestmentDoesNotCreateOperationalControl ()

------------------------------------------------------------------------
-- The current highest-value residual is account-level tracing, not another
-- generic name sweep.
------------------------------------------------------------------------

data FlowDebt : Set where
  southernTrustDailyBalanceLedger : FlowDebt
  valarCapitalCallDocuments : FlowDebt
  valarLimitedPartnerTerms : FlowDebt
  sourceSpecificTracingModel : FlowDebt
  honeycombUnderlyingPortfolio : FlowDebt
  boothbayUnderlyingPortfolio : FlowDebt

record FlowAcquisition : Set where
  constructor flow-acquisition
  field
    debt : FlowDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open FlowAcquisition public

canonicalFlowAcquisition : List FlowAcquisition
canonicalFlowAcquisition =
  flow-acquisition southernTrustDailyBalanceLedger 100 true
    "Acquire Southern Trust bank statements/daily balances and same-day settlement records sufficient to test source-specific tracing rather than treating fungible inflows as earmarked."
  ∷ flow-acquisition valarCapitalCallDocuments 100 true
    "Acquire the full Valar II/III subscription agreements, capital-call notices and commitment schedules for Southern Trust to reconcile transaction-chart outflows with contractual commitments."
  ∷ flow-acquisition valarLimitedPartnerTerms 99 true
    "Resolve commitment size, LP rights, side letters, distributions and exit/value history for Southern Trust's Valar II/III interests."
  ∷ flow-acquisition sourceSpecificTracingModel 99 true
    "Only after bank-balance acquisition, test FIFO/LIFO/same-day or legally appropriate tracing rules; do not infer Black/Rothschild-funded Valar from entity continuity alone."
  ∷ flow-acquisition honeycombUnderlyingPortfolio 95 true
    "Resolve Honeycomb Partners/Ventures investment objects and Epstein/Southern Trust governance rights."
  ∷ flow-acquisition boothbayUnderlyingPortfolio 94 true
    "Resolve Boothbay fund subscriptions, redemptions, distributions and any overlapping counterparties."
  ∷ []
