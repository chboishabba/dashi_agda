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
-- Economic object: fungible-capital capacity, not dollar-by-dollar earmarking.
--
-- If an entity receives large inflows and independently makes investments,
-- those inflows contribute to the entity's fungible capital pool and therefore
-- to its deployment capacity.  This is enough for balance-sheet/systemic
-- incidence analysis.  It does NOT establish that any particular payer
-- instructed, earmarked or specifically financed any particular downstream
-- investment.
--
-- Commitment, contributed capital, capital-account value, distributions and
-- realised exit proceeds remain separate quantities.
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

valarIIChartFlows : List FundFlow
valarIIChartFlows =
  fund-flow "2015-01-21" southernTrust valarGlobalII 150000 "DB-SDNY-0004346" true
  ∷ fund-flow "2015-02-12" southernTrust valarGlobalII 900000 "DB-SDNY-0004412" true
  ∷ fund-flow "2015-03-20" southernTrust valarGlobalII 2700000 "DB-SDNY-0004487" true
  ∷ fund-flow "2015-07-24" southernTrust valarGlobalII 600000 "DB-SDNY-0004790" true
  ∷ fund-flow "2015-09-24" southernTrust valarGlobalII 1950000 "DB-SDNY-0004924" true
  ∷ []

valarIIIChartFlows : List FundFlow
valarIIIChartFlows =
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

record ValarChartAggregate : Set where
  constructor valar-chart-aggregate
  field
    locatedFundIIChartRowsUSD : Nat
    locatedFundIIIChartRowsUSD : Nat
    combinedLocatedChartRowsUSD : Nat
    source : String
    chartIsExhaustiveLedger : Bool
open ValarChartAggregate public

canonicalValarChartAggregate : ValarChartAggregate
canonicalValarChartAggregate = valar-chart-aggregate
  6300000 22500000 28800000
  "Selected/highlighted Deutsche Bank transaction chart in EFTA00080250..252"
  false

record ValarLPState : Set where
  constructor valar-lp-state
  field
    fund : InvestmentEntity
    asOf : String
    commitmentUSD : Nat
    paidInUSD : Nat
    unfundedUSD : Nat
    endingPartnerCapitalUSD : Nat
    source : String
    audited : Bool
open ValarLPState public

valarII20150930 : ValarLPState
valarII20150930 = valar-lp-state
  valarGlobalII "2015-09-30" 15000000 4350000 10650000 4147529
  "EFTA00597489 — Valar Fund II unaudited Southern Trust LP statement"
  false

valarII20180630 : ValarLPState
valarII20180630 = valar-lp-state
  valarGlobalII "2018-06-30" 15000000 14550000 450000 21000471
  "EFTA00811795/96 — Valar Fund II unaudited Southern Trust LP statement"
  false

valarIII20170803 : ValarLPState
valarIII20170803 = valar-lp-state
  valarGlobalIII "2017-08-03" 25000000 15000000 10000000 0
  "EFTA00591792 — Valar Fund III capital-call notice; partner-capital value not supplied by this document"
  false

record ValarCommitmentBoundary : Set where
  constructor valar-commitment-boundary
  field
    fundIICommitmentUSD : Nat
    fundIIICommitmentUSD : Nat
    combinedCommitmentUSD : Nat
    fundII2018PaidUSD : Nat
    fundIII2018PaidUSD : Nat
    combined2018PaidUSD : Nat
    commitmentEqualsCashPaid : Bool
    cashPaidEqualsCapitalAccountValue : Bool
    capitalAccountEqualsRealisedExit : Bool
open ValarCommitmentBoundary public

canonicalValarCommitmentBoundary : ValarCommitmentBoundary
canonicalValarCommitmentBoundary = valar-commitment-boundary
  15000000 25000000 40000000
  14550000 21000000 35550000
  false false false

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
-- Fungible capital-pool model.
------------------------------------------------------------------------

record CapitalPoolState : Set where
  constructor capital-pool-state
  field
    blackInflowsPaid : Bool
    rothschildInflowsPaid : Bool
    otherInflowsPossible : Bool
    valarDeploymentsPaid : Bool
    honeycombDeploymentsPaid : Bool
    boothbayDeploymentsPaid : Bool
    inflowsIncreaseFungibleCapacity : Bool
    specificPayerEarmarkedSpecificInvestment : Bool
    payerControlledDownstreamInvestment : Bool
open CapitalPoolState public

canonicalCapitalPoolState : CapitalPoolState
canonicalCapitalPoolState = capital-pool-state
  true true true true true true true false false

record SouthernTrustFlowBoundary : Set where
  constructor southern-trust-flow-boundary
  field
    blackInflowReceiptsExist : Bool
    rothschildInflowReceiptsExist : Bool
    valarOutflowReceiptsExist : Bool
    southernTrustIsValarLimitedPartner : Bool
    sameEntityCapitalPoolPathExists : Bool
    inflowContributionToPoolPaid : Bool
    downstreamDeploymentFromPoolPaid : Bool
    blackEarmarkedValarFundingPaid : Bool
    rothschildEarmarkedValarFundingPaid : Bool
    commonRecipientCreatesCommonPurpose : Bool
open SouthernTrustFlowBoundary public

canonicalSouthernTrustFlowBoundary : SouthernTrustFlowBoundary
canonicalSouthernTrustFlowBoundary = southern-trust-flow-boundary
  true true true true true true true false false false

data FungiblePoolContributionImpliesEarmarking : Set where
data CommonRecipientImpliesCommonPurpose : Set where
data FundInvestmentImpliesOperationalControl : Set where
data CommitmentImpliesPaidCapital : Set where
data CapitalAccountValueImpliesRealisedCash : Set where

fungibleContributionDoesNotCreateEarmarking : FungiblePoolContributionImpliesEarmarking → ⊥
fungibleContributionDoesNotCreateEarmarking ()

commonRecipientDoesNotCreateCommonPurpose : CommonRecipientImpliesCommonPurpose → ⊥
commonRecipientDoesNotCreateCommonPurpose ()

fundInvestmentDoesNotCreateOperationalControl : FundInvestmentImpliesOperationalControl → ⊥
fundInvestmentDoesNotCreateOperationalControl ()

commitmentDoesNotCreatePaidCapital : CommitmentImpliesPaidCapital → ⊥
commitmentDoesNotCreatePaidCapital ()

capitalAccountDoesNotCreateRealisedCash : CapitalAccountValueImpliesRealisedCash → ⊥
capitalAccountDoesNotCreateRealisedCash ()

------------------------------------------------------------------------
-- Acquisition is now economic-capacity and fund-rights reconstruction.
------------------------------------------------------------------------

data FlowDebt : Set where
  southernTrustCapitalizationTimeline : FlowDebt
  valarFundIICompleteCallLedger : FlowDebt
  valarFundIIICompleteCallLedger : FlowDebt
  valarLimitedPartnerTerms : FlowDebt
  valarDistributionExitHistory : FlowDebt
  capitalPoolDeploymentChronology : FlowDebt
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
  flow-acquisition southernTrustCapitalizationTimeline 100 true
    "Reconstruct Southern Trust's capitalization and liquidity timeline from major inflows, revenues, distributions and investment calls. The object is fungible deployment capacity, not earmarked-dollar tracing."
  ∷ flow-acquisition valarFundIIICompleteCallLedger 100 true
    "Reconstruct every Fund III capital call/wire and reconcile to the USD 25m commitment and paid-in capital."
  ∷ flow-acquisition valarFundIICompleteCallLedger 99 true
    "Reconstruct the complete Fund II call ledger and reconcile the transaction record to the USD 15m commitment and paid-in capital."
  ∷ flow-acquisition valarLimitedPartnerTerms 99 true
    "Resolve subscription agreements, LP rights, side letters, governance, fee terms and any special arrangements for Southern Trust's Valar II/III interests."
  ∷ flow-acquisition valarDistributionExitHistory 99 true
    "Separate unrealised partner-capital/valuation gains from actual distributions and trace the ultimate estate disposition/expiry of the Valar interests."
  ∷ flow-acquisition capitalPoolDeploymentChronology 98 true
    "Join major inflow periods to aggregate deployment intensity across Valar, Honeycomb, Boothbay and other vehicles without assigning fungible dollars to specific payers absent earmarking evidence."
  ∷ flow-acquisition honeycombUnderlyingPortfolio 95 true
    "Resolve Honeycomb Partners/Ventures investment objects and Epstein/Southern Trust governance rights."
  ∷ flow-acquisition boothbayUnderlyingPortfolio 94 true
    "Resolve Boothbay fund subscriptions, redemptions, distributions and any overlapping counterparties."
  ∷ []
