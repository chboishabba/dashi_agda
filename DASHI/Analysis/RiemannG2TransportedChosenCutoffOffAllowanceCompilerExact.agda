module DASHI.Analysis.RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Intermediate
import DASHI.Analysis.RiemannG2PoleQuotientOffChosenCutoffCompilerExact as Chosen
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment

------------------------------------------------------------------------
-- TRANSPORTED CHECKED CUTOFF + ONE NEAR THEOREM -> FINAL OFF PAYMENT
--
-- This is the current preferred final Off compiler.  It combines the exact
-- trust boundary and the exact consumer boundary:
--
--   checked Lean split/far theorem --(proof transport)--> Agda final carrier
--   nearResponse(J) <= B_near(J)                 [new analytic theorem]
--   B_far(J) <= epsilon                          [cutoff/far receipt]
--   B_near(J) + epsilon <= A_off                 [new near slack theorem]
--
-- and compiles the final PoleQuotientOffAllowancePayment at that one J.
------------------------------------------------------------------------

record TransportedChosenCutoffOffAllowanceInput
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    chosenCutoff : Transport.Cutoff transport

    CrossingCutoff : Transport.Cutoff transport -> Set
    chosenCutoffCrosses : CrossingCutoff chosenCutoff

    nearUpperAtChosen : Transport.FiniteNearUpperAt transport chosenCutoff

    intermediateFarAllowance : NearFar.Scalar S

    nearBudgetSelfOrder :
      NearFar._≤_ S
        (Transport.nearBudgetAt transport chosenCutoff)
        (Transport.nearBudgetAt transport chosenCutoff)

    farBudgetBelowIntermediateAllowance :
      NearFar._≤_ S
        (Transport.farBudgetAt transport chosenCutoff)
        intermediateFarAllowance

    assignedOffAllowance : NearFar.Scalar S

    nearBudgetPlusIntermediateBelowAssigned :
      NearFar._≤_ S
        (NearFar.add S
          (Transport.nearBudgetAt transport chosenCutoff)
          intermediateFarAllowance)
        assignedOffAllowance

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    producerReference : String

open TransportedChosenCutoffOffAllowanceInput public

chosenNearFarBudget :
  forall {S transport} ->
  TransportedChosenCutoffOffAllowanceInput S transport ->
  NearFar.NearFarOffOrdinateBudget S
chosenNearFarBudget {transport = transport} input =
  Transport.compileNearFarBudgetAt
    transport
    (chosenCutoff input)
    (nearUpperAtChosen input)

chosenIntermediateFit :
  forall {S transport} ->
  (input : TransportedChosenCutoffOffAllowanceInput S transport) ->
  Intermediate.IntermediateNearFarAllowanceFit
    S
    (chosenNearFarBudget input)
    (assignedOffAllowance input)
chosenIntermediateFit input = record
  { Intermediate.intermediateFarAllowance = intermediateFarAllowance input
  ; Intermediate.nearBudgetSelfOrder = nearBudgetSelfOrder input
  ; Intermediate.farBudgetBelowIntermediateAllowance =
      farBudgetBelowIntermediateAllowance input
  ; Intermediate.nearBudgetPlusIntermediateBelowAssigned =
      nearBudgetPlusIntermediateBelowAssigned input
  }

chosenCombinedBudgetBelowAssigned :
  forall {S transport} ->
  (input : TransportedChosenCutoffOffAllowanceInput S transport) ->
  NearFar._≤_ S
    (NearFar.add S
      (NearFar.nearBudget (chosenNearFarBudget input))
      (NearFar.farBudget (chosenNearFarBudget input)))
    (assignedOffAllowance input)
chosenCombinedBudgetBelowAssigned {S = S} input =
  Intermediate.compiledNearPlusFarBelowAssigned
    S
    (chosenNearFarBudget input)
    (assignedOffAllowance input)
    (chosenIntermediateFit input)

chosenOffBudget :
  forall {S transport} ->
  TransportedChosenCutoffOffAllowanceInput S transport ->
  Transport.Taper transport ->
  NearFar.Scalar S
chosenOffBudget {S = S} {transport = transport} input taper =
  NearFar.add S
    (Transport.nearBudgetAt transport (chosenCutoff input))
    (Transport.farBudgetAt transport (chosenCutoff input))

compileChosenCutoffInput :
  forall {S transport} ->
  TransportedChosenCutoffOffAllowanceInput S transport ->
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
  TransportedChosenCutoffOffAllowanceInput S transport ->
  Payment.PoleQuotientOffAllowancePayment
compileFinalOffAllowancePayment input =
  Chosen.compilePoleQuotientOffAllowancePayment
    (compileChosenCutoffInput input)

------------------------------------------------------------------------
-- Final Off theorem boundary.
------------------------------------------------------------------------

record TransportedChosenCutoffOffBoundary : Set where
  constructor transported-chosen-cutoff-off-boundary
  field
    allCutoffNearUpperFamilyRequired : Bool
    allCutoffNearUpperFamilyRequiredIsFalse :
      allCutoffNearUpperFamilyRequired ≡ false

    checkedLeanStatusBooleanSufficientWithoutAgdaTransport : Bool
    checkedLeanStatusBooleanSufficientWithoutAgdaTransportIsFalse :
      checkedLeanStatusBooleanSufficientWithoutAgdaTransport ≡ false

    oneAgdaSplitFarTransportRequired : Bool
    oneAgdaSplitFarTransportRequiredIsTrue :
      oneAgdaSplitFarTransportRequired ≡ true

    oneChosenNearUpperRequired : Bool
    oneChosenNearUpperRequiredIsTrue :
      oneChosenNearUpperRequired ≡ true

    farBudgetMustFitIntermediateAllowance : Bool
    farBudgetMustFitIntermediateAllowanceIsTrue :
      farBudgetMustFitIntermediateAllowance ≡ true

    nearBudgetMustLeaveIntermediateAllowance : Bool
    nearBudgetMustLeaveIntermediateAllowanceIsTrue :
      nearBudgetMustLeaveIntermediateAllowance ≡ true

    finalOffPaymentCompilesAfterTheseReceipts : Bool
    finalOffPaymentCompilesAfterTheseReceiptsIsTrue :
      finalOffPaymentCompilesAfterTheseReceipts ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalTransportedChosenCutoffOffBoundary :
  TransportedChosenCutoffOffBoundary
canonicalTransportedChosenCutoffOffBoundary =
  transported-chosen-cutoff-off-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "The final Off payment no longer requires a near/far budget family over all cutoffs. Transport the checked Lean every-cutoff split/far theorem into the final Agda carrier once, select the one crossing cutoff J actually consumed, prove the finite near upper there, prove the selected far budget fits epsilon, and prove B_near(J)+epsilon <= A_off. The chosen-cutoff and intermediate-allowance compilers then construct the final PoleQuotientOffAllowancePayment. Status Booleans alone remain non-proof-bearing, and RH is not derived."
