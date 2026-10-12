module DASHI.Economics.AITerminalPayerConsumerSufficiency20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact as Microsoft

------------------------------------------------------------------------
-- CONSUMER-RELATIVE TERMINAL-PAYER SUFFICIENCY
--
-- Cross-pollination from the scoped-verifier / future-sufficiency lane: an
-- evidence bundle is sufficient only relative to a declared consumer question.
-- The selected Microsoft path answers a narrow capacity/provenance question;
-- it does not answer exhaustive CoreWeave terminal-independence.
------------------------------------------------------------------------

data TerminalPayerConsumer : Set where
  selectedMicrosoftExternalCashCapacity : TerminalPayerConsumer
  exhaustiveCoreWeaveTerminalIndependence : TerminalPayerConsumer
  circularRevenueExclusion : TerminalPayerConsumer

data ConsumerPaymentState : Set where
  paid partial open : ConsumerPaymentState

consumerPaymentState : TerminalPayerConsumer → ConsumerPaymentState
consumerPaymentState selectedMicrosoftExternalCashCapacity = paid
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

exhaustiveCoreWeaveIndependenceReceipt :
  ConsumerRelativePayerReceipt exhaustiveCoreWeaveTerminalIndependence
exhaustiveCoreWeaveIndependenceReceipt = consumer-relative-payer-receipt
  "selected Microsoft path is insufficient for exhaustive payer-graph independence"
  open true true false false

selectedMicrosoftCapacityConsumerPaid :
  consumerPaymentState selectedMicrosoftExternalCashCapacity ≡ paid
selectedMicrosoftCapacityConsumerPaid = refl

coreWeaveExhaustiveIndependenceConsumerOpen :
  consumerPaymentState exhaustiveCoreWeaveTerminalIndependence ≡ open
coreWeaveExhaustiveIndependenceConsumerOpen = refl

selectedCapacityReusesSourcePaidBoundary :
  Microsoft.selectedNamedPayerExternalCashCapacity
    Microsoft.coreWeaveMicrosoftTerminalPayerBoundary ≡ true
selectedCapacityReusesSourcePaidBoundary = Microsoft.selectedNamedPayerCapacityIsPaid

exhaustiveBoundaryReusesOpenWholeGraph :
  Microsoft.completeTerminalPayerProvenanceClosed
    Microsoft.coreWeaveMicrosoftTerminalPayerBoundary ≡ false
exhaustiveBoundaryReusesOpenWholeGraph = Microsoft.completeTerminalPayerProvenanceStillOpen

data SelectedPayerCapacityCreatesExhaustiveIndependence : Set where
data ConsumerPaidCreatesAllConsumerPayments : Set where

selectedPayerCapacityDoesNotCreateExhaustiveIndependence :
  SelectedPayerCapacityCreatesExhaustiveIndependence → ⊥
selectedPayerCapacityDoesNotCreateExhaustiveIndependence ()

oneConsumerPaymentDoesNotPayEveryConsumer :
  ConsumerPaidCreatesAllConsumerPayments → ⊥
oneConsumerPaymentDoesNotPayEveryConsumer ()

consumerRelativeTerminalBoundary : String
consumerRelativeTerminalBoundary =
  "Terminal-payer evidence is consumer-relative: the Microsoft path pays the narrow question whether one major named CoreWeave payer has independently generated external-customer cash capacity. It does not pay exhaustive CoreWeave terminal independence, contract realisation, or exclusion of every financing/counterparty loop."
