module DASHI.Economics.AIContractBackedFinancingReplication20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryFiledCompanyDisclosure : Source.SourceKind
primaryFiledCompanyDisclosure = Source.namedSourceKind "company disclosure filed with SEC"

nebiusFiledFinancing : Source.AttributedSource
nebiusFiledFinancing = Source.mkNoDOISource
  "Nebius Group N.V."
  "Nebius raises $775 million in first secured debt financing to accelerate global buildout"
  "SEC-filed company exhibit"
  "2026-07-17"
  "https://www.sec.gov/Archives/edgar/data/1513845/000110465926084452/tm2620683d1_ex99-1.htm"
  primaryFiledCompanyDisclosure
  "Nebius disclosed an approximately 775 million dollar senior secured facility backed by deployed GPU infrastructure and contracted cash flows from an investment-grade customer, maturing 2030-10-31 and priced at SOFR plus 250 basis points; together with customer cash flows, the facility was said to cover more than 100 percent of underlying GPU capex."
  Source.publicAttribution

irenFiledMicrosoftContract : Source.AttributedSource
irenFiledMicrosoftContract = Source.mkNoDOISource
  "IREN Limited"
  "Annual Report / Microsoft GPU services contract disclosure"
  "SEC-filed company report"
  "2026-06-30"
  "https://www.sec.gov/Archives/edgar/data/1878848/000187884826000052/iren-20260630.htm"
  primaryFiledCompanyDisclosure
  "IREN disclosed an approximately 9.7 billion dollar Microsoft GPU-services contract through 2031, delivered in four tranches, with 20 percent of the contract value for each tranche paid prior to the applicable delivery date and credited against later service fees."
  Source.publicAttribution

sharonAIFiledFacility : Source.AttributedSource
sharonAIFiledFacility = Source.mkNoDOISource
  "SharonAI Holdings Inc."
  "Sharon AI Enters Into GPU-Backed Debt Facility, Expanding Funding Flexibility for AI Factory Deployments"
  "SEC-filed company exhibit"
  "2026-10-01"
  "https://www.sec.gov/Archives/edgar/data/2068385/000149315226045368/ex99-1.htm"
  primaryFiledCompanyDisclosure
  "Sharon AI disclosed a 356 million dollar committed senior secured GPU-backed SPV debt facility at a fixed 9.95 percent rate, secured against GPUs and associated cash flows, with proceeds supporting compute infrastructure dedicated to customer contracts."
  Source.publicAttribution

aibNebiusFiledDevelopment : Source.AttributedSource
aibNebiusFiledDevelopment = Source.mkNoDOISource
  "AIB Data Centers Inc."
  "AIB Data Centers Signs Contract with Nebius for AI Data Center Capacity"
  "SEC-filed company exhibit"
  "2026-09-30"
  "https://www.sec.gov/Archives/edgar/data/2070542/000121390026105865/ea030737801ex99-1.htm"
  primaryFiledCompanyDisclosure
  "AIB disclosed a binding 12-year 50 MW agreement with Nebius and said customer prepayments under the initial term, together with project-level debt and preferred equity, were expected to fund a substantial portion of initial development costs and reduce the anticipated need for corporate-level common equity."
  Source.publicAttribution

record FinancingReplication : Set where
  constructor financing-replication
  field
    issuer : String
    gpuAndContractCashBackDebt : Bool
    customerPrepaymentBeforeDelivery : Bool
    investmentGradeCustomerReferenced : Bool
    debtPricingBasisPointsOverSOFR : Nat
    customerCashPlusDebtCoversCapex : Bool
    exactProjectReturnPaid : Bool
    terminalCustomerIndependencePaid : Bool
    circularFinancingEstablished : Bool

open FinancingReplication public

nebiusReplication : FinancingReplication
nebiusReplication = financing-replication
  "Nebius" true false true 250 true false false false

irenReplication : FinancingReplication
irenReplication = financing-replication
  "IREN" false true true 0 false false false false

record InfrastructureFinanceLayerReplication : Set where
  constructor infrastructure-finance-layer-replication
  field
    subject : String
    gpuBackedSPVDebt : Bool
    developerCustomerPrepayment : Bool
    projectDebtPlusPreferredEquity : Bool
    contractCashCollateralOrFunding : Bool
    fixedCashInterestBasisPoints : Nat
    realisedProjectReturnPaid : Bool
    terminalDemandPaid : Bool
    circularityPaid : Bool

open InfrastructureFinanceLayerReplication public

sharonAIReplication : InfrastructureFinanceLayerReplication
sharonAIReplication = infrastructure-finance-layer-replication
  "Sharon AI" true false false true 995 false false false

aibNebiusDeveloperReplication : InfrastructureFinanceLayerReplication
aibNebiusDeveloperReplication = infrastructure-finance-layer-replication
  "AIB/Nebius 50 MW developer layer" false true true true 0 false false false

nebiusContractBackedDebtPaid : gpuAndContractCashBackDebt nebiusReplication ≡ true
nebiusContractBackedDebtPaid = refl

irenPrepaymentPaid : customerPrepaymentBeforeDelivery irenReplication ≡ true
irenPrepaymentPaid = refl

sharonGPUBackedSPVDebtPaid : gpuBackedSPVDebt sharonAIReplication ≡ true
sharonGPUBackedSPVDebtPaid = refl

aibDeveloperPrepaymentPaid : developerCustomerPrepayment aibNebiusDeveloperReplication ≡ true
aibDeveloperPrepaymentPaid = refl

aibProjectFinancePaid : projectDebtPlusPreferredEquity aibNebiusDeveloperReplication ≡ true
aibProjectFinancePaid = refl

crossCompanyMechanismReplication : Bool
crossCompanyMechanismReplication = true

crossCompanyReplicationPaid : crossCompanyMechanismReplication ≡ true
crossCompanyReplicationPaid = refl

crossLayerMechanismReplication : Bool
crossLayerMechanismReplication = true

crossLayerReplicationPaid : crossLayerMechanismReplication ≡ true
crossLayerReplicationPaid = refl

data MechanismReplicationImpliesCircularFinancingPermission : Set where
data ContractCoverageImpliesPositiveReturnPermission : Set where
data CustomerPrepaymentImpliesTerminalIndependencePermission : Set where
data CrossLayerReplicationImpliesCommonEconomicsPermission : Set where

replicationDoesNotCreateCircularFinancing : MechanismReplicationImpliesCircularFinancingPermission → ⊥
replicationDoesNotCreateCircularFinancing ()

capexCoverageDoesNotCreatePositiveReturn : ContractCoverageImpliesPositiveReturnPermission → ⊥
capexCoverageDoesNotCreatePositiveReturn ()

prepaymentDoesNotCreateTerminalIndependence : CustomerPrepaymentImpliesTerminalIndependencePermission → ⊥
prepaymentDoesNotCreateTerminalIndependence ()

crossLayerReplicationDoesNotCreateCommonEconomics : CrossLayerReplicationImpliesCommonEconomicsPermission → ⊥
crossLayerReplicationDoesNotCreateCommonEconomics ()

boundary : String
boundary =
  "Primary SEC-filed company disclosures now show customer/contract-linked infrastructure financing replicated across several layers rather than only across neoclouds. Nebius disclosed secured debt backed by GPU infrastructure and contracted cash flows from an investment-grade customer; IREN disclosed Microsoft tranche prepayments before delivery; Sharon AI disclosed a GPU-backed SPV facility secured on GPUs and associated customer cash flows; and AIB disclosed a Nebius data-centre project expected to use customer prepayments plus project debt and preferred equity to fund much of development. This pays cross-company and cross-layer replication of financing mechanisms only. Filed company statements retain authority for their disclosed terms; DASHI owns the typed comparison. Mechanism replication does not establish common project economics, terminal demand, circular financing, fraud, distress or a bubble."
