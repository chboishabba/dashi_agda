module DASHI.Economics.AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- COREWEAVE -> MICROSOFT SELECTED TERMINAL-PAYER BOUNDARY
--
-- Primary filings pay a named contractual CoreWeave payer path and separately
-- pay Microsoft external-customer cash generation.  This closes a selected
-- payer-capacity/provenance coordinate, not complete CoreWeave terminal-payer
-- independence: the CoreWeave payments are conditional/future, cash is
-- fungible, and the rest of the payer/counterparty graph is not exhaustively
-- traced.
------------------------------------------------------------------------

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

coreWeaveSeptember2026Source : Source.AttributedSource
coreWeaveSeptember2026Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "September 18 2026 filing"
  "SEC filing"
  "2026-09-18"
  "https://www.sec.gov/Archives/edgar/data/2110365/000119312526395475/ck0002110365-20260918.htm"
  secFilingKind
  "primary carrier for Microsoft statements of work providing up to approximately USD 43.8B of payments through December 2033 subject to delivery and service-availability requirements"
  Source.publicAttribution

microsoftFY2026Source : Source.AttributedSource
microsoftFY2026Source = Source.mkNoDOISource
  "Microsoft Corporation"
  "Annual Report for fiscal year ended June 30 2026"
  "SEC Form 10-K"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/789019/000119312526323660/msft-20260630.htm"
  secFilingKind
  "primary carrier for FY2026 operating cash flow USD 182.9B, Microsoft Cloud revenue USD 214.4B, commercial RPO USD 678B, and the statement that higher operating cash reflected increased cash received from customers"
  Source.publicAttribution

record NamedPayerContract : Set where
  constructor namedPayerContract
  field
    provider : String
    payer : String
    maximumPaymentsMillionUSD : Nat
    endDate : String
    conditionalOnDeliveryAvailability : Bool
    paymentsFullyRealised : Bool
    source : Source.AttributedSource

open NamedPayerContract public

coreWeaveMicrosoftContract : NamedPayerContract
coreWeaveMicrosoftContract = namedPayerContract
  "CoreWeave" "Microsoft" 43800 "2033-12"
  true false coreWeaveSeptember2026Source

record ExternalCustomerCashObservation : Set where
  constructor externalCustomerCashObservation
  field
    company : String
    fiscalYear : String
    operatingCashFlowMillionUSD : Nat
    cloudRevenueMillionUSD : Nat
    commercialRPOMillionUSD : Nat
    cashIncreaseAttributedToCustomerReceipts : Bool
    externallyGeneratedCustomerCashObserved : Bool
    source : Source.AttributedSource

open ExternalCustomerCashObservation public

microsoftFY2026ExternalCash : ExternalCustomerCashObservation
microsoftFY2026ExternalCash = externalCustomerCashObservation
  "Microsoft" "FY2026" 182900 214400 678000 true true microsoftFY2026Source

record TerminalPayerBoundary : Set where
  constructor terminalPayerBoundary
  field
    namedProviderPayerPathAcquired : Bool
    namedPayerExternalCustomerCashObserved : Bool
    selectedNamedPayerExternalCashCapacity : Bool
    contractPaymentsRealised : Bool
    completeTerminalPayerProvenanceClosed : Bool
    allCounterpartyFundingLoopsExcluded : Bool
    circularRevenueEstablished : Bool

open TerminalPayerBoundary public

coreWeaveMicrosoftTerminalPayerBoundary : TerminalPayerBoundary
coreWeaveMicrosoftTerminalPayerBoundary = terminalPayerBoundary
  true true true false false false false

selectedNamedPayerCapacityIsPaid :
  selectedNamedPayerExternalCashCapacity coreWeaveMicrosoftTerminalPayerBoundary ≡ true
selectedNamedPayerCapacityIsPaid = refl

contractPaymentsStillNotRealised :
  contractPaymentsRealised coreWeaveMicrosoftTerminalPayerBoundary ≡ false
contractPaymentsStillNotRealised = refl

completeTerminalPayerProvenanceStillOpen :
  completeTerminalPayerProvenanceClosed coreWeaveMicrosoftTerminalPayerBoundary ≡ false
completeTerminalPayerProvenanceStillOpen = refl

circularRevenueStillNotEstablished :
  circularRevenueEstablished coreWeaveMicrosoftTerminalPayerBoundary ≡ false
circularRevenueStillNotEstablished = refl

data ExternalCashCapacityImpliesRealisedPaymentPermission : Set where
data NamedPayerCapacityImpliesCompleteTerminalIndependencePermission : Set where
data ContractPlusExternalCashImpliesNoCircularityPermission : Set where

externalCashCapacityDoesNotAutoRealiseContract :
  ExternalCashCapacityImpliesRealisedPaymentPermission → ⊥
externalCashCapacityDoesNotAutoRealiseContract ()

namedPayerCapacityDoesNotCloseWholeGraph :
  NamedPayerCapacityImpliesCompleteTerminalIndependencePermission → ⊥
namedPayerCapacityDoesNotCloseWholeGraph ()

contractAndExternalCashDoNotAutoDisproveCircularity :
  ContractPlusExternalCashImpliesNoCircularityPermission → ⊥
contractAndExternalCashDoNotAutoDisproveCircularity ()

boundary : String
boundary =
  "A named CoreWeave payer path to Microsoft is source-paid, and Microsoft independently reports large customer-derived FY2026 operating cash and cloud revenue. This pays selected named-payer external-cash capacity/provenance. It does not prove the conditional CoreWeave contract has been fully realised, exhaustively trace all CoreWeave payers, or exclude every financing/counterparty loop."
