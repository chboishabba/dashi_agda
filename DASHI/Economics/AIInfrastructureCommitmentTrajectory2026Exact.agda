module DASHI.Economics.AIInfrastructureCommitmentTrajectory2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- INFRASTRUCTURE COMMITMENT TRAJECTORIES
--
-- These are heterogeneous accounting commitments.  Same-company/same-metric
-- changes may be compared; heterogeneous totals are not summed into a synthetic
-- 'AI liability' without a harmonized accounting scope.
------------------------------------------------------------------------

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

nvidiaQ22027Source : Source.AttributedSource
nvidiaQ22027Source = Source.mkNoDOISource
  "NVIDIA Corporation" "Quarterly report for fiscal Q2 2027" "SEC Form 10-Q" "2026"
  "https://www.sec.gov/Archives/edgar/data/1045810/000104581026000075/nvda-20260726.htm"
  secFilingKind
  "primary carrier for USD 279B supply/capacity commitments versus USD 119B prior quarter and USD 366B total disclosed future commitments"
  Source.publicAttribution

oracleFY2026Source : Source.AttributedSource
oracleFY2026Source = Source.mkNoDOISource
  "Oracle Corporation" "Fiscal 2026 Q4 results" "SEC exhibit" "2026"
  "https://www.sec.gov/Archives/edgar/data/1341439/000119312526265848/orcl-ex99_1.htm"
  secFilingKind
  "primary carrier for USD 638B RPO, USD 75B customer-prepaid/customer-supplied AI hardware, FY2026 financing and expected FY2027 capital raising"
  Source.publicAttribution

microsoftFY2026Source : Source.AttributedSource
microsoftFY2026Source = Source.mkNoDOISource
  "Microsoft Corporation" "Annual Report for fiscal year ended June 30 2026" "SEC Form 10-K" "2026"
  "https://www.sec.gov/Archives/edgar/data/789019/000119312526323660/msft-20260630.htm"
  secFilingKind
  "primary carrier for broad contractual obligations and the statement that cloud/AI investment occurs ahead of fully developed revenue streams"
  Source.publicAttribution

alphabetQ22026Source : Source.AttributedSource
alphabetQ22026Source = Source.mkNoDOISource
  "Alphabet Inc." "Quarterly report for quarter ended June 30 2026" "SEC Form 10-Q" "2026"
  "https://www.sec.gov/Archives/edgar/data/1652044/000165204426000071/goog-20260630.htm"
  secFilingKind
  "primary carrier for H1 capex, purchase commitments, lease commitments, equity/debt financing and guarantee/credit-derivative exposures"
  Source.publicAttribution

coreWeaveSupplierSource : Source.AttributedSource
coreWeaveSupplierSource = Source.mkNoDOISource
  "CoreWeave, Inc." "2026 supplier/related-party filing" "SEC filing" "2026-04-22"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000191/crwv-20260422.htm"
  secFilingKind
  "primary carrier for all-current-GPU NVIDIA reliance, NVIDIA 17% of 2025 supplier purchases and related role-overlap context"
  Source.publicAttribution

record SameMetricCommitmentTrajectory : Set where
  constructor sameMetricCommitmentTrajectory
  field
    company : String
    metric : String
    earlierBillionUSD : Nat
    laterBillionUSD : Nat
    laterGreater : Bool
    source : Source.AttributedSource

open SameMetricCommitmentTrajectory public

nvidiaSupplyCapacityTrajectory : SameMetricCommitmentTrajectory
nvidiaSupplyCapacityTrajectory = sameMetricCommitmentTrajectory
  "NVIDIA" "supply and capacity commitments" 119 279 true nvidiaQ22027Source

record CustomerFundedCapacity : Set where
  constructor customerFundedCapacity
  field
    company : String
    rpoBillionUSD : Nat
    customerPrepaidOrSuppliedHardwareBillionUSD : Nat
    reducesProviderCapitalNeed : Bool
    establishesIndependentTerminalCash : Bool
    source : Source.AttributedSource

open CustomerFundedCapacity public

oracleCustomerFundedAIHardware : CustomerFundedCapacity
oracleCustomerFundedAIHardware = customerFundedCapacity
  "Oracle" 638 75 true false oracleFY2026Source

record BroadCommitmentStack : Set where
  constructor broadCommitmentStack
  field
    company : String
    totalOrHeadlineBillionUSD : Nat
    accountingScope : String
    aiOnly : Bool
    source : Source.AttributedSource

open BroadCommitmentStack public

microsoftBroadContractualStack : BroadCommitmentStack
microsoftBroadContractualStack = broadCommitmentStack
  "Microsoft" 744 "broad contractual obligations including leases, purchase, construction and interest payments" false microsoftFY2026Source

alphabetBroadPurchaseCommitments : BroadCommitmentStack
alphabetBroadPurchaseCommitments = broadCommitmentStack
  "Alphabet" 811 "purchase commitments and other contractual obligations, primarily technical infrastructure and inventory with other categories" false alphabetQ22026Source

record SupplierInvestorOverlap : Set where
  constructor supplierInvestorOverlap
  field
    platform : String
    supplierInvestor : String
    soleCurrentGPUArchitecture : Bool
    supplierPurchaseShareBp : Nat
    equityInvestmentBillionUSD : Nat
    circularRevenueEstablished : Bool
    source : Source.AttributedSource

open SupplierInvestorOverlap public

coreWeaveNvidiaSupplierInvestorOverlap : SupplierInvestorOverlap
coreWeaveNvidiaSupplierInvestorOverlap = supplierInvestorOverlap
  "CoreWeave" "NVIDIA" true 1700 2 false coreWeaveSupplierSource

------------------------------------------------------------------------
-- Accounting-scope firewalls.
------------------------------------------------------------------------

data HeterogeneousCommitmentsMayBeSummedPermission : Set where
data CustomerPrepaymentImpliesTerminalDemandPermission : Set where
data SupplierInvestorOverlapImpliesCircularRevenuePermission : Set where

data LargeCommitmentImpliesInsolvencyPermission : Set where

heterogeneousCommitmentsDoNotAutoSum : HeterogeneousCommitmentsMayBeSummedPermission → ⊥
heterogeneousCommitmentsDoNotAutoSum ()

customerPrepaymentDoesNotAutoProveTerminalDemand : CustomerPrepaymentImpliesTerminalDemandPermission → ⊥
customerPrepaymentDoesNotAutoProveTerminalDemand ()

supplierInvestorOverlapDoesNotAutoProveCircularRevenue : SupplierInvestorOverlapImpliesCircularRevenuePermission → ⊥
supplierInvestorOverlapDoesNotAutoProveCircularRevenue ()

largeCommitmentDoesNotAutoProveInsolvency : LargeCommitmentImpliesInsolvencyPermission → ⊥
largeCommitmentDoesNotAutoProveInsolvency ()

oracleCustomerFundingStillNotTerminal : establishesIndependentTerminalCash oracleCustomerFundedAIHardware ≡ false
oracleCustomerFundingStillNotTerminal = refl

coreWeaveNvidiaOverlapStillNotCircularRevenue : circularRevenueEstablished coreWeaveNvidiaSupplierInvestorOverlap ≡ false
coreWeaveNvidiaOverlapStillNotCircularRevenue = refl
