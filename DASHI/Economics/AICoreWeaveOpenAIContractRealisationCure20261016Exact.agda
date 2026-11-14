module DASHI.Economics.AICoreWeaveOpenAIContractRealisationCure20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secKind : Source.SourceKind
secKind = Source.namedSourceKind "SEC-filed credit agreement / amendment"

coreWeaveDDTL3InitialSource : Source.AttributedSource
coreWeaveDDTL3InitialSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Current Report and DDTL 3.0 Credit Agreement"
  "SEC filing"
  "2025-07-28"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962825000033/crwv-20250728.htm"
  secKind
  "DDTL 3.0 finances the OpenAI/Phoenix 1 customer contract; the Contract Realization Ratio compares actual amounts billed or received over the most recent three-month period with projected contracted cash flows and has a 0.85x covenant floor"
  Source.publicAttribution

coreWeaveDDTL3AmendmentSource : Source.AttributedSource
coreWeaveDDTL3AmendmentSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "First Amendment to DDTL 3.0 Credit Agreement and Parent Guarantee and Pledge Agreement"
  "SEC filing"
  "2025-12-31"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000104/ex10311.htm"
  secKind
  "postpones initial Contract Realization Ratio testing to February 28 2026 and permits unlimited equity cures for the relevant financial covenants before October 28 2026, with limits thereafter"
  Source.publicAttribution

record ContractRealisationCureState : Set where
  constructor contract-realisation-cure-state
  field
    contractRealisationFloorBp : Nat
    initialTestingDate : String
    unlimitedEquityCuresBefore20261028 : Bool
    equityCureCanRepairCovenantMetric : Bool
    equityCureIsCustomerPayment : Bool
    publicRealisedContractRatio : Bool
    publicOpenAICustomerCashAmount : Bool
    covenantFailureOccurred : Bool
    defaultOccurred : Bool

open ContractRealisationCureState public

coreWeaveOpenAIContractRealisationCure : ContractRealisationCureState
coreWeaveOpenAIContractRealisationCure = contract-realisation-cure-state
  8500 "2026-02-28" true true false false false false false

contractRealisationFloorBpIs8500 :
  contractRealisationFloorBp coreWeaveOpenAIContractRealisationCure ≡ 8500
contractRealisationFloorBpIs8500 = refl

testingPostponedTo20260228 :
  initialTestingDate coreWeaveOpenAIContractRealisationCure ≡ "2026-02-28"
testingPostponedTo20260228 = refl

unlimitedEquityCuresThrough20261027Paid :
  unlimitedEquityCuresBefore20261028 coreWeaveOpenAIContractRealisationCure ≡ true
unlimitedEquityCuresThrough20261027Paid = refl

equityCureCanRepairCovenantMetric :
  ContractRealisationCureState.equityCureCanRepairCovenantMetric coreWeaveOpenAIContractRealisationCure ≡ true
equityCureCanRepairCovenantMetric = refl

realisedContractRatioStillPrivate :
  publicRealisedContractRatio coreWeaveOpenAIContractRealisationCure ≡ false
realisedContractRatioStillPrivate = refl

data EquityCureCreatesOpenAICustomerCashPermission : Set where
data CureAvailabilityProvesCovenantFailurePermission : Set where

equityCureDoesNotCreateOpenAICustomerCash : EquityCureCreatesOpenAICustomerCashPermission → ⊥
equityCureDoesNotCreateOpenAICustomerCash ()

cureAvailabilityDoesNotProveCovenantFailure : CureAvailabilityProvesCovenantFailurePermission → ⊥
cureAvailabilityDoesNotProveCovenantFailure ()

boundary : String
boundary =
  "The OpenAI/Phoenix 1 DDTL 3.0 financing has a source-paid 0.85x Contract Realization Ratio covenant comparing actual billings/receipts with projected contracted cash flows. A filed amendment postpones initial testing to February 28 2026 and permits unlimited equity cures before October 28 2026, with tighter limits thereafter. This establishes a concrete mechanism by which parent equity can repair the covenant calculation when the customer-contract realization metric is deficient. An equity cure is not OpenAI customer cash and does not prove that a shortfall, covenant breach, default or cure actually occurred. The realised ratio and named customer-cash amounts remain private/unpublished in the acquired public evidence."
