module DASHI.Economics.AICoreWeaveCustomerCreditFinancingCoupling20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secCreditKind : Source.SourceKind
secCreditKind = Source.namedSourceKind "SEC-filed credit agreement / issuer filing"

ddtl4CreditAgreementSource : Source.AttributedSource
ddtl4CreditAgreementSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "DDTL 4.0 Credit Agreement, Exhibit 10.1"
  "SEC-filed credit agreement"
  "2026-03-30"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000129/ex1011.htm"
  secCreditKind
  "defines Funding Date GPU Amount as 90 percent of Funding Date Capital Expenditures plus eligible transaction costs; financed GPU/infrastructure supports a Master Service Agreement"
  Source.publicAttribution

ddtl2CustomerCreditSource : Source.AttributedSource
ddtl2CustomerCreditSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Annual meeting / proxy debt disclosure for DDTL 2.0"
  "SEC filing"
  "2026-04-22"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000191/crwv-20260422.htm"
  secCreditKind
  "borrowing availability is limited to a percentage of depreciated GPU-server purchase price with the percentage based on the credit rating of the applicable customer; SOFR margins also vary with that customer credit rating"
  Source.publicAttribution

record CustomerCreditFinancingCoupling : Set where
  constructor customer-credit-financing-coupling
  field
    ddtl4FundingDateCapexAdvanceBp : Nat
    ddtl2MarginDependsOnCustomerCredit : Bool
    ddtl2AvailabilityDependsOnDepreciatedGPUCostAndCustomerCredit : Bool
    customerContractBacked : Bool
    customerCreditTransmitsIntoFinancingTerms : Bool
    contractBackedDebtCreatesTerminalCash : Bool
    customerDefaultImpliesLenderLossOneForOne : Bool
    projectReturnPaid : Bool

open CustomerCreditFinancingCoupling public

coreWeaveCustomerCreditFinancing : CustomerCreditFinancingCoupling
coreWeaveCustomerCreditFinancing = customer-credit-financing-coupling
  9000 true true true true false false false

ddtl4FundingDateCapexAdvanceBpIs9000 :
  ddtl4FundingDateCapexAdvanceBp coreWeaveCustomerCreditFinancing ≡ 9000
ddtl4FundingDateCapexAdvanceBpIs9000 = refl

ddtl2MarginDependsOnCustomerCreditReceipt :
  ddtl2MarginDependsOnCustomerCredit coreWeaveCustomerCreditFinancing ≡ true
ddtl2MarginDependsOnCustomerCreditReceipt = refl

ddtl2AvailabilityDependsOnDepreciatedGPUCostAndCustomerCreditReceipt :
  ddtl2AvailabilityDependsOnDepreciatedGPUCostAndCustomerCredit coreWeaveCustomerCreditFinancing ≡ true
ddtl2AvailabilityDependsOnDepreciatedGPUCostAndCustomerCreditReceipt = refl

customerCreditTransmitsIntoFinancingTermsReceipt :
  customerCreditTransmitsIntoFinancingTerms coreWeaveCustomerCreditFinancing ≡ true
customerCreditTransmitsIntoFinancingTermsReceipt = refl

data ContractBackedDebtCreatesTerminalCashPermission : Set where
data CustomerCreditCouplingCreatesProjectReturnPermission : Set where

contractBackedDebtDoesNotCreateTerminalCash : ContractBackedDebtCreatesTerminalCashPermission → ⊥
contractBackedDebtDoesNotCreateTerminalCash ()

customerCreditCouplingDoesNotCreateProjectReturn : CustomerCreditCouplingCreatesProjectReturnPermission → ⊥
customerCreditCouplingDoesNotCreateProjectReturn ()

boundary : String
boundary =
  "Primary CoreWeave financing documents expose a literal customer-credit-to-GPU-financing transmission channel. DDTL 4.0 defines a funding-date GPU amount using 90 percent of funding-date capital expenditures plus eligible transaction costs. DDTL 2.0 ties borrowing availability to depreciated GPU purchase cost and the applicable customer's credit rating, and ties borrowing margins to that customer rating as well. This pays structural financial dependence between customer contract quality and asset-level financing terms. It does not establish realised customer cash, one-for-one default transmission, project profitability, terminal demand independence or a universal company-wide leverage ratio."
