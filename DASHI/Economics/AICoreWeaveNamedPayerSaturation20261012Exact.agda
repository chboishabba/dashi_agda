module DASHI.Economics.AICoreWeaveNamedPayerSaturation20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact as Microsoft
import DASHI.Economics.AICoreWeaveMicrosoftHistoricalRevenue20261016Exact as Historical

------------------------------------------------------------------------
-- COREWEAVE NAMED-PAYER EDGE SATURATION
--
-- Historical Microsoft recognised revenue is source-paid for 2025. Current
-- 2026 top-customer shares remain anonymised and are not de-anonymised from
-- historical or future named relationships.
------------------------------------------------------------------------

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

coreWeaveQ22026Source : Source.AttributedSource
coreWeaveQ22026Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  secFilingKind
  "primary carrier for anonymised Q2 customer shares 36/26/10 percent and named future-significant-customer contracts: OpenAI up to approximately USD 6.5B through May 31 2031 and Meta initially up to approximately USD 21.0B through December 20 2032; customer letters may represent different customers across periods"
  Source.publicAttribution

metaQ22026Source : Source.AttributedSource
metaQ22026Source = Source.mkNoDOISource
  "Meta Platforms, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/1326801/000162828026050705/meta-20260630.htm"
  secFilingKind
  "primary carrier for H1-2026 operating cash flow USD 64.088B and statement that the year-over-year increase was driven primarily by increased cash collections from customers due to higher revenue"
  Source.publicAttribution

record NamedPayerEdge : Set where
  constructor named-payer-edge
  field
    provider : String
    payer : String
    maximumContractPaymentsMillionUSD : Nat
    contractEnd : String
    contractEdgeSourcePaid : Bool
    externalCustomerCashObserved : Bool
    operatingCashFlowMillionUSD : Nat
    customerCashCollectionsObserved : Bool
    contractPaymentsRealised : Bool

open NamedPayerEdge public

metaEdge : NamedPayerEdge
metaEdge = named-payer-edge
  "CoreWeave" "Meta Platforms" 21000 "2032-12-20"
  true true 64088 true false

openAIEdge : NamedPayerEdge
openAIEdge = named-payer-edge
  "CoreWeave" "OpenAI" 6500 "2031-05-31"
  true false 0 false false

record PayerSaturationState : Set where
  constructor payer-saturation-state
  field
    microsoftNamedEdgePaid : Bool
    microsoftExternalCashPaid : Bool
    microsoftHistoricalRecognisedRevenuePaid : Bool
    metaNamedEdgePaid : Bool
    metaExternalCashPaid : Bool
    openAINamedEdgePaid : Bool
    openAIExternalCashPaid : Bool
    currentTopThreeSharesPaid : Bool
    currentTopThreeIdentitiesPaid : Bool
    exhaustiveTerminalGraphClosed : Bool

open PayerSaturationState public

coreWeavePayerSaturation : PayerSaturationState
coreWeavePayerSaturation = payer-saturation-state
  true true true true true true false true false false

microsoftExternalCashEdgePaid :
  Microsoft.selectedNamedPayerExternalCashCapacity Microsoft.coreWeaveMicrosoftTerminalPayerBoundary ≡ true
microsoftExternalCashEdgePaid = Microsoft.selectedNamedPayerCapacityIsPaid

microsoftHistoricalRecognisedRevenueEdgePaid :
  Historical.historicalNamedRevenue Historical.coreWeaveMicrosoft2025Revenue ≡ true
microsoftHistoricalRecognisedRevenueEdgePaid = Historical.historicalNamedRevenuePaid

metaExternalCashEdgePaid : externalCustomerCashObserved metaEdge ≡ true
metaExternalCashEdgePaid = refl

openAIContractEdgePaidCashProvenanceOpen : contractEdgeSourcePaid openAIEdge ≡ true
openAIContractEdgePaidCashProvenanceOpen = refl

openAIExternalCashStillOpen : externalCustomerCashObserved openAIEdge ≡ false
openAIExternalCashStillOpen = refl

anonymousCurrentTopCustomerIdentityStillOpen : currentTopThreeIdentitiesPaid coreWeavePayerSaturation ≡ false
anonymousCurrentTopCustomerIdentityStillOpen = refl

data TwoNamedExternalCashEdgesCloseWholeGraphPermission : Set where
data FutureContractIdentifiesCurrentAnonymousCustomerPermission : Set where
data HistoricalNamedRevenueIdentifiesCurrentAnonymousCustomerPermission : Set where
data ContractCommitmentImpliesRealisedPaymentPermission : Set where

twoNamedExternalCashEdgesDoNotCloseWholeGraph : TwoNamedExternalCashEdgesCloseWholeGraphPermission → ⊥
twoNamedExternalCashEdgesDoNotCloseWholeGraph ()

futureNamedContractDoesNotIdentifyCurrentAnonymousCustomer : FutureContractIdentifiesCurrentAnonymousCustomerPermission → ⊥
futureNamedContractDoesNotIdentifyCurrentAnonymousCustomer ()

historicalNamedRevenueDoesNotIdentifyCurrentAnonymousCustomer : HistoricalNamedRevenueIdentifiesCurrentAnonymousCustomerPermission → ⊥
historicalNamedRevenueDoesNotIdentifyCurrentAnonymousCustomer ()

contractCommitmentDoesNotCreateRealisedPayment : ContractCommitmentImpliesRealisedPaymentPermission → ⊥
contractCommitmentDoesNotCreateRealisedPayment ()

boundary : String
boundary =
  "CoreWeave now has a historical named realised-revenue edge for Microsoft in 2025, plus two named payer edges with independently source-paid external-customer cash-generation capacity in this programme: Microsoft and Meta. OpenAI is a source-paid named contract edge but lacks an equivalent public external-cash receipt here. The Q2-2026 realised top-customer shares 36/26/10 percent remain anonymised and CoreWeave warns customer-letter identities can differ across periods, so neither the historical Microsoft identity nor future named contracts are used to relabel Customer A/B/C. Recognised revenue is not payer-specific cash collection; named external cash capacity is not proof a particular CoreWeave invoice was paid; the terminal-payer graph remains incomplete."
