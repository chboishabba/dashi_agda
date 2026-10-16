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

nebiusContractBackedDebtPaid : gpuAndContractCashBackDebt nebiusReplication ≡ true
nebiusContractBackedDebtPaid = refl

irenPrepaymentPaid : customerPrepaymentBeforeDelivery irenReplication ≡ true
irenPrepaymentPaid = refl

crossCompanyMechanismReplication : Bool
crossCompanyMechanismReplication = true

crossCompanyReplicationPaid : crossCompanyMechanismReplication ≡ true
crossCompanyReplicationPaid = refl

data MechanismReplicationImpliesCircularFinancingPermission : Set where
data ContractCoverageImpliesPositiveReturnPermission : Set where
data CustomerPrepaymentImpliesTerminalIndependencePermission : Set where

replicationDoesNotCreateCircularFinancing : MechanismReplicationImpliesCircularFinancingPermission → ⊥
replicationDoesNotCreateCircularFinancing ()

capexCoverageDoesNotCreatePositiveReturn : ContractCoverageImpliesPositiveReturnPermission → ⊥
capexCoverageDoesNotCreatePositiveReturn ()

prepaymentDoesNotCreateTerminalIndependence : CustomerPrepaymentImpliesTerminalIndependencePermission → ⊥
prepaymentDoesNotCreateTerminalIndependence ()

boundary : String
boundary =
  "Primary SEC-filed company disclosures show that customer/contract-linked infrastructure financing is not unique to CoreWeave. Nebius disclosed secured debt backed by GPU infrastructure and contracted cash flows from an investment-grade customer, with customer cash plus the facility described as covering more than 100 percent of underlying GPU capex. IREN disclosed a large Microsoft GPU-services contract with 20 percent tranche prepayments before delivery. This pays cross-company replication of the financing mechanism class only. Company-filed promotional language is not independent proof of economics; capex coverage is not project return; customer prepayment is not terminal independence; and repeated contract-backed financing does not establish circular financing, fraud, distress or a bubble."
