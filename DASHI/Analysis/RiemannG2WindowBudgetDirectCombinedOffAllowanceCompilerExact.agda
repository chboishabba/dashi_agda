module DASHI.Analysis.RiemannG2WindowBudgetDirectCombinedOffAllowanceCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as Minimal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2WindowBudgetToTransportedNearUpperExact as WindowTransport
import DASHI.Analysis.RiemannG2TransportedChosenCutoffDirectCombinedAllowanceExact as Direct
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment

------------------------------------------------------------------------
-- SELECTED TARGET-WINDOW PAYMENT + SAME-OBJECT TRANSPORT
-- + DIRECT CHOSEN-CUTOFF COMBINED FIT -> FINAL OFF PAYMENT
--
-- A SelectedFiniteNearBudgetPayment already owns the finite-near theorem on the
-- exact target window.  WindowBudgetTransportAttachment moves that theorem once
-- to the transported cutoff coordinates.  Therefore the caller should not also
-- provide a separately manufactured FiniteNearUpperAt.
------------------------------------------------------------------------

record WindowBudgetDirectCombinedOffAllowanceInput
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (payment : Minimal.SelectedFiniteNearBudgetPayment space formula window)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    chosenCutoff : Transport.Cutoff transport

    CrossingCutoff : Transport.Cutoff transport -> Set
    chosenCutoffCrosses : CrossingCutoff chosenCutoff

    windowTransport :
      WindowTransport.WindowBudgetTransportAttachment
        space formula window payment S transport chosenCutoff

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

open WindowBudgetDirectCombinedOffAllowanceInput public

compileDirectCombinedInput :
  forall {space formula window payment S transport} ->
  WindowBudgetDirectCombinedOffAllowanceInput
    space formula window payment S transport ->
  Direct.DirectCombinedTransportedOffAllowanceInput S transport
compileDirectCombinedInput input = record
  { Direct.chosenCutoff = chosenCutoff input
  ; Direct.CrossingCutoff = CrossingCutoff input
  ; Direct.chosenCutoffCrosses = chosenCutoffCrosses input
  ; Direct.nearUpperAtChosen =
      WindowTransport.compileFiniteNearUpperAt (windowTransport input)
  ; Direct.assignedOffAllowance = assignedOffAllowance input
  ; Direct.chosenCombinedBudgetBelowAssigned =
      chosenCombinedBudgetBelowAssigned input
  ; Direct.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameLiteralPoleQuotientTaperAsFinalConsumer input
  ; Direct.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input
  ; Direct.producerReference = producerReference input
  }

compileFinalOffAllowancePayment :
  forall {space formula window payment S transport} ->
  WindowBudgetDirectCombinedOffAllowanceInput
    space formula window payment S transport ->
  Payment.PoleQuotientOffAllowancePayment
compileFinalOffAllowancePayment input =
  Direct.compileFinalOffAllowancePayment (compileDirectCombinedInput input)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record WindowBudgetDirectCombinedOffBoundary : Set where
  constructor window-budget-direct-combined-off-boundary
  field
    secondFiniteNearEvaluationRequired : Bool
    secondFiniteNearEvaluationRequiredIsFalse :
      secondFiniteNearEvaluationRequired ≡ false

    separatelyManufacturedTransportedNearUpperRequired : Bool
    separatelyManufacturedTransportedNearUpperRequiredIsFalse :
      separatelyManufacturedTransportedNearUpperRequired ≡ false

    selectedWindowSameObjectTransportStillRequired : Bool
    selectedWindowSameObjectTransportStillRequiredIsTrue :
      selectedWindowSameObjectTransportStillRequired ≡ true

    directCombinedChosenBudgetFitStillRequired : Bool
    directCombinedChosenBudgetFitStillRequiredIsTrue :
      directCombinedChosenBudgetFitStillRequired ≡ true

    intermediateFarAllowanceFactorizationRequired : Bool
    intermediateFarAllowanceFactorizationRequiredIsFalse :
      intermediateFarAllowanceFactorizationRequired ≡ false

    finalOffPaymentCompiles : Bool
    finalOffPaymentCompilesIsTrue : finalOffPaymentCompiles ≡ true

    finalOffPaymentInhabitedHere : Bool
    finalOffPaymentInhabitedHereIsFalse : finalOffPaymentInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalWindowBudgetDirectCombinedOffBoundary :
  WindowBudgetDirectCombinedOffBoundary
canonicalWindowBudgetDirectCombinedOffBoundary =
  window-budget-direct-combined-off-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "Once a SelectedFiniteNearBudgetPayment exists on the exact PoleNearTargetWindow, reuse WindowBudgetTransportAttachment to generate the transported chosen-cutoff near upper. Do not re-evaluate the finite sum and do not ask the caller to manufacture another near-upper record. The remaining theorem-bearing Off fit on this preferred producer route is the literal direct combined inequality B_near(J)+B_far(J)<=A_off at the selected crossing cutoff, plus the existing same-object/taper receipts. No intermediate epsilon factorization, Off payment inhabitant or RH theorem is fabricated here."
