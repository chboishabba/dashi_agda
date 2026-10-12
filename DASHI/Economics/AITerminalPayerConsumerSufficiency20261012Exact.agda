module DASHI.Economics.AITerminalPayerConsumerSufficiency20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact as Microsoft
import DASHI.Economics.AICoreWeaveNamedPayerSaturation20261012Exact as Saturation

------------------------------------------------------------------------
-- CONSUMER-RELATIVE TERMINAL-PAYER SUFFICIENCY
--
-- Evidence sufficiency is indexed by the question being answered.  Microsoft
-- and Meta now pay narrow external-cash-capacity consumers; OpenAI pays contract
-- identity but not external-cash provenance.  None of those selected consumers
-- pays exhaustive CoreWeave terminal independence.
------------------------------------------------------------------------

data TerminalPayerConsumer : Set where
  selectedMicrosoftExternalCashCapacity : TerminalPayerConsumer
  selectedMetaExternalCashCapacity : TerminalPayerConsumer
  selectedOpenAIExternalCashCapacity : TerminalPayerConsumer
  exhaustiveCoreWeaveTerminalIndependence : TerminalPayerConsumer
  circularRevenueExclusion : TerminalPayerConsumer

data ConsumerPaymentState : Set where
  paid partial open : ConsumerPaymentState

consumerPaymentState : TerminalPayerConsumer → ConsumerPaymentState
consumerPaymentState selectedMicrosoftExternalCashCapacity = paid
consumerPaymentState selectedMetaExternalCashCapacity = paid
consumerPaymentState selectedOpenAIExternalCashCapacity = open
consumerPaymentState exhaustiveCoreWeaveTerminalIndependence = open
consumerPaymentState circularRevenueExclusion = open

record ConsumerRelativePayerReceipt (consumer : TerminalPayerConsumer) : Set where
  constructor consumer-relative-payer-receipt
  field
    evidenceRef : String
    payment : ConsumerPaymentState
    sameNamedPayerPathAcquired : Bool
    namedPayerExternalCashObserved : Bool
    completeGraphTraced : Bool
    everyFundingLoopExcluded : Bool

open ConsumerRelativePayerReceipt public

selectedMicrosoftCapacityReceipt :
  ConsumerRelativePayerReceipt selectedMicrosoftExternalCashCapacity
selectedMicrosoftCapacityReceipt = consumer-relative-payer-receipt
  "CoreWeave -> Microsoft contract plus Microsoft FY2026 external-customer cash observation"
  paid true true false false

selectedMetaCapacityReceipt :
  ConsumerRelativePayerReceipt selectedMetaExternalCashCapacity
selectedMetaCapacityReceipt = consumer-relative-payer-receipt
  "CoreWeave -> Meta contract plus Meta H1-2026 external-customer cash observation"
  paid true true false false

selectedOpenAICashReceipt :
  ConsumerRelativePayerReceipt selectedOpenAIExternalCashCapacity
selectedOpenAICashReceipt = consumer-relative-payer-receipt
  "CoreWeave -> OpenAI named contract edge is source-paid; equivalent public external-customer cash provenance remains open"
  open true false false false

exhaustiveCoreWeaveIndependenceReceipt :
  ConsumerRelativePayerReceipt exhaustiveCoreWeaveTerminalIndependence
exhaustiveCoreWeaveIndependenceReceipt = consumer-relative-payer-receipt
  "selected Microsoft/Meta/OpenAI edges are insufficient for exhaustive payer-graph independence"
  open true true false false

selectedMicrosoftCapacityConsumerPaid :
  consumerPaymentState selectedMicrosoftExternalCashCapacity ≡ paid
selectedMicrosoftCapacityConsumerPaid = refl

selectedMetaCapacityConsumerPaid :
  consumerPaymentState selectedMetaExternalCashCapacity ≡ paid
selectedMetaCapacityConsumerPaid = refl

selectedOpenAICashConsumerOpen :
  consumerPaymentState selectedOpenAIExternalCashCapacity ≡ open
selectedOpenAICashConsumerOpen = refl

coreWeaveExhaustiveIndependenceConsumerOpen :
  consumerPaymentState exhaustiveCoreWeaveTerminalIndependence ≡ open
coreWeaveExhaustiveIndependenceConsumerOpen = refl

selectedMicrosoftCapacityReusesSourcePaidBoundary :
  Microsoft.selectedNamedPayerExternalCashCapacity
    Microsoft.coreWeaveMicrosoftTerminalPayerBoundary ≡ true
selectedMicrosoftCapacityReusesSourcePaidBoundary = Microsoft.selectedNamedPayerCapacityIsPaid

selectedMetaCapacityReusesSourcePaidBoundary :
  Saturation.externalCustomerCashObserved Saturation.metaEdge ≡ true
selectedMetaCapacityReusesSourcePaidBoundary = Saturation.metaExternalCashEdgePaid

selectedOpenAIExternalCashReusesOpenBoundary :
  Saturation.externalCustomerCashObserved Saturation.openAIEdge ≡ false
selectedOpenAIExternalCashReusesOpenBoundary = Saturation.openAIExternalCashStillOpen

exhaustiveBoundaryReusesOpenWholeGraph :
  Microsoft.completeTerminalPayerProvenanceClosed
    Microsoft.coreWeaveMicrosoftTerminalPayerBoundary ≡ false
exhaustiveBoundaryReusesOpenWholeGraph = Microsoft.completeTerminalPayerProvenanceStillOpen

data SelectedPayerCapacityCreatesExhaustiveIndependence : Set where
data ConsumerPaidCreatesAllConsumerPayments : Set where

data NamedContractCreatesExternalCashPermission : Set where

selectedPayerCapacityDoesNotCreateExhaustiveIndependence :
  SelectedPayerCapacityCreatesExhaustiveIndependence → ⊥
selectedPayerCapacityDoesNotCreateExhaustiveIndependence ()

oneConsumerPaymentDoesNotPayEveryConsumer :
  ConsumerPaidCreatesAllConsumerPayments → ⊥
oneConsumerPaymentDoesNotPayEveryConsumer ()

namedContractDoesNotCreateExternalCashProvenance :
  NamedContractCreatesExternalCashPermission → ⊥
namedContractDoesNotCreateExternalCashProvenance ()

consumerRelativeTerminalBoundary : String
consumerRelativeTerminalBoundary =
  "Terminal-payer evidence is consumer-relative. Microsoft and Meta pay narrow questions asking whether those named CoreWeave counterparties have independently observed external-customer cash capacity. OpenAI pays a named contractual edge but not that cash-provenance consumer. None of these selected payments establishes contract realisation, identifies the anonymised current top customers, exhaustively traces the CoreWeave payer graph, or excludes every financing/counterparty loop."
