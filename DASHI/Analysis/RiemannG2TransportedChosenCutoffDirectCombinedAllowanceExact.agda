module DASHI.Analysis.RiemannG2TransportedChosenCutoffDirectCombinedAllowanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2PoleQuotientOffChosenCutoffCompilerExact as Chosen
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact as Factored

------------------------------------------------------------------------
-- TRANSPORTED CHECKED CUTOFF + ONE NEAR THEOREM + DIRECT COMBINED FIT
--   -> FINAL OFF PAYMENT
--
-- The final chosen-cutoff consumer does not require an intermediate far
-- allowance decomposition.  It consumes exactly one theorem
--
--   B_near(J) + B_far(J) <= A_off
--
-- on the one selected crossing cutoff.  Therefore the historical factorization
--
--   B_far(J) <= epsilon
--   B_near(J) + epsilon <= A_off
--
-- together with the reflexive near self-order is only a sufficient producer of
-- the literal combined fit, not part of the least-privilege terminal API.
------------------------------------------------------------------------

record DirectCombinedTransportedOffAllowanceInput
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    chosenCutoff : Transport.Cutoff transport

    CrossingCutoff : Transport.Cutoff transport -> Set
    chosenCutoffCrosses : CrossingCutoff chosenCutoff

    nearUpperAtChosen : Transport.FiniteNearUpperAt transport chosenCutoff

    assignedOffAllowance : NearFar.Scalar S

    chosenCombinedBudgetBelowAssigned :
      NearFar._≤_ S
        (NearFar.add S
          (Transport.nearBudgetAt transport chosenCutoff)
          (Transport.farBudgetAt transport chosenCutoff))
        assignedOffAllowance

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    producerReference : String

open DirectCombinedTransportedOffAllowanceInput public

chosenNearFarBudget :
  forall {S transport} ->
  DirectCombinedTransportedOffAllowanceInput S transport ->
  NearFar.NearFarOffOrdinateBudget S
chosenNearFarBudget {transport = transport} input =
  Transport.compileNearFarBudgetAt
    transport
    (chosenCutoff input)
    (nearUpperAtChosen input)

chosenOffBudget :
  forall {S transport} ->
  DirectCombinedTransportedOffAllowanceInput S transport ->
  Transport.Taper transport ->
  NearFar.Scalar S
chosenOffBudget {S = S} {transport = transport} input taper =
  NearFar.add S
    (Transport.nearBudgetAt transport (chosenCutoff input))
    (Transport.farBudgetAt transport (chosenCutoff input))

compileChosenCutoffInput :
  forall {S transport} ->
  DirectCombinedTransportedOffAllowanceInput S transport ->
  Chosen.ChosenCutoffPoleQuotientOffAllowanceInput S
compileChosenCutoffInput {S = S} {transport = transport} input = record
  { Chosen.Taper = Transport.Taper transport
  ; Chosen.Cutoff = Transport.Cutoff transport
  ; Chosen.universalPoleQuotientTaper =
      Transport.universalPoleQuotientTaper transport
  ; Chosen.chosenCutoff = chosenCutoff input
  ; Chosen.CrossingCutoff = CrossingCutoff input
  ; Chosen.chosenCutoffCrosses = chosenCutoffCrosses input
  ; Chosen.OffResponse = Transport.fullResponse transport
  ; Chosen.OffBudget = chosenOffBudget input
  ; Chosen.chosenNearFarBudget = chosenNearFarBudget input
  ; Chosen.offResponseAtUniversalIsChosenFull = refl
  ; Chosen.offBudgetAtUniversalIsChosenCombinedBudget = refl
  ; Chosen.assignedOffAllowance = assignedOffAllowance input
  ; Chosen.chosenCombinedBudgetBelowAssignedAllowance =
      chosenCombinedBudgetBelowAssigned input
  ; Chosen.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameLiteralPoleQuotientTaperAsFinalConsumer input
  ; Chosen.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input
  ; Chosen.producerReference = producerReference input
  }

compileFinalOffAllowancePayment :
  forall {S transport} ->
  DirectCombinedTransportedOffAllowanceInput S transport ->
  Payment.PoleQuotientOffAllowancePayment
compileFinalOffAllowancePayment input =
  Chosen.compilePoleQuotientOffAllowancePayment
    (compileChosenCutoffInput input)

------------------------------------------------------------------------
-- HISTORICAL FACTORED ROUTE IS A SUFFICIENT PRODUCER OF THE SMALLER INPUT
------------------------------------------------------------------------

fromFactoredInput :
  forall {S transport} ->
  Factored.TransportedChosenCutoffOffAllowanceInput S transport ->
  DirectCombinedTransportedOffAllowanceInput S transport
fromFactoredInput input = record
  { chosenCutoff = Factored.chosenCutoff input
  ; CrossingCutoff = Factored.CrossingCutoff input
  ; chosenCutoffCrosses = Factored.chosenCutoffCrosses input
  ; nearUpperAtChosen = Factored.nearUpperAtChosen input
  ; assignedOffAllowance = Factored.assignedOffAllowance input
  ; chosenCombinedBudgetBelowAssigned =
      Factored.chosenCombinedBudgetBelowAssigned input
  ; sameLiteralPoleQuotientTaperAsFinalConsumer =
      Factored.sameLiteralPoleQuotientTaperAsFinalConsumer input
  ; sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      Factored.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input
  ; producerReference = Factored.producerReference input
  }

factoredInputCompilesFinalPayment :
  forall {S transport} ->
  Factored.TransportedChosenCutoffOffAllowanceInput S transport ->
  Payment.PoleQuotientOffAllowancePayment
factoredInputCompilesFinalPayment input =
  compileFinalOffAllowancePayment (fromFactoredInput input)

------------------------------------------------------------------------
-- LEAST-PRIVILEGE BOUNDARY
------------------------------------------------------------------------

record DirectCombinedTransportedOffBoundary : Set where
  constructor direct-combined-transported-off-boundary
  field
    intermediateFarAllowancePrimitiveRequired : Bool
    intermediateFarAllowancePrimitiveRequiredIsFalse :
      intermediateFarAllowancePrimitiveRequired ≡ false

    nearBudgetSelfOrderPrimitiveRequired : Bool
    nearBudgetSelfOrderPrimitiveRequiredIsFalse :
      nearBudgetSelfOrderPrimitiveRequired ≡ false

    separateFarFitPrimitiveRequired : Bool
    separateFarFitPrimitiveRequiredIsFalse :
      separateFarFitPrimitiveRequired ≡ false

    separateNearSlackPrimitiveRequired : Bool
    separateNearSlackPrimitiveRequiredIsFalse :
      separateNearSlackPrimitiveRequired ≡ false

    directChosenCombinedFitAccepted : Bool
    directChosenCombinedFitAcceptedIsTrue :
      directChosenCombinedFitAccepted ≡ true

    historicalFactoredRouteStillSufficient : Bool
    historicalFactoredRouteStillSufficientIsTrue :
      historicalFactoredRouteStillSufficient ≡ true

    oneChosenNearUpperStillRequired : Bool
    oneChosenNearUpperStillRequiredIsTrue :
      oneChosenNearUpperStillRequired ≡ true

    crossProverSplitFarTransportStillRequired : Bool
    crossProverSplitFarTransportStillRequiredIsTrue :
      crossProverSplitFarTransportStillRequired ≡ true

    finalOffPaymentCompilesAfterDirectCombinedFit : Bool
    finalOffPaymentCompilesAfterDirectCombinedFitIsTrue :
      finalOffPaymentCompilesAfterDirectCombinedFit ≡ true

    offPaymentInhabitedHere : Bool
    offPaymentInhabitedHereIsFalse : offPaymentInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalDirectCombinedTransportedOffBoundary :
  DirectCombinedTransportedOffBoundary
canonicalDirectCombinedTransportedOffBoundary =
  direct-combined-transported-off-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The literal final chosen-cutoff consumer needs one transported near upper and one direct theorem B_near(J)+B_far(J)<=A_off. Intermediate epsilon, reflexive near self-order, a separate far-fit theorem and a separate near-slack theorem are only one sufficient factorization and are not primitive terminal payments. The existing factored route projects mechanically to this smaller input. Cross-prover split/far transport, the selected near upper, crossing-cutoff identity and same-final-taper receipt remain genuine prerequisites. No Off payment or RH theorem is fabricated here."
