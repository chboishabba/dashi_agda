module DASHI.Analysis.RiemannG2WindowBudgetDirectCombinedOffAnalyticCoreExact where

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
import DASHI.Analysis.RiemannG2TransportedDirectCombinedOffAnalyticCoreExact as DirectCore
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

------------------------------------------------------------------------
-- EXACT TARGET-WINDOW PAYMENT -> CLAY-FACING OFF ANALYTIC CORE
--
-- This is the preferred concrete sufficient producer after the least-privilege
-- reductions.  The selected window payment already owns the finite-near upper;
-- its same-object/order attachment transports that theorem to one cutoff J.
-- The only fresh scalar theorem added here is the direct combined allowance fit.
-- Crossing identity and final-taper identity are deliberately absent because
-- they belong to OffRepresentationAttachment, not OffAnalyticCore.
------------------------------------------------------------------------

record WindowBudgetDirectCombinedOffCoreInput
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (payment : Minimal.SelectedFiniteNearBudgetPayment space formula window)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    chosenCutoff : Transport.Cutoff transport

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

    analyticReference : String

open WindowBudgetDirectCombinedOffCoreInput public

compileDirectCoreInput :
  forall {space formula window payment S transport} ->
  WindowBudgetDirectCombinedOffCoreInput
    space formula window payment S transport ->
  DirectCore.DirectCombinedTransportedOffCoreInput S transport
compileDirectCoreInput input = record
  { DirectCore.chosenCutoff = chosenCutoff input
  ; DirectCore.nearUpperAtChosen =
      WindowTransport.compileFiniteNearUpperAt (windowTransport input)
  ; DirectCore.assignedOffAllowance = assignedOffAllowance input
  ; DirectCore.chosenCombinedBudgetBelowAssigned =
      chosenCombinedBudgetBelowAssigned input
  ; DirectCore.analyticReference = analyticReference input
  }

compileOffAnalyticCore :
  forall {space formula window payment S transport} ->
  WindowBudgetDirectCombinedOffCoreInput
    space formula window payment S transport ->
  Core.OffAnalyticCore
compileOffAnalyticCore input =
  DirectCore.compileOffAnalyticCore (compileDirectCoreInput input)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record WindowBudgetDirectCombinedOffCoreBoundary : Set where
  constructor window-budget-direct-combined-off-core-boundary
  field
    secondFiniteNearEvaluationRequired : Bool
    secondFiniteNearEvaluationRequiredIsFalse :
      secondFiniteNearEvaluationRequired ≡ false

    separatelyManufacturedNearUpperRequired : Bool
    separatelyManufacturedNearUpperRequiredIsFalse :
      separatelyManufacturedNearUpperRequired ≡ false

    selectedWindowSameObjectOrderTransportRequired : Bool
    selectedWindowSameObjectOrderTransportRequiredIsTrue :
      selectedWindowSameObjectOrderTransportRequired ≡ true

    crossingReceiptRequiredByAnalyticCore : Bool
    crossingReceiptRequiredByAnalyticCoreIsFalse :
      crossingReceiptRequiredByAnalyticCore ≡ false

    finalTaperReceiptRequiredByAnalyticCore : Bool
    finalTaperReceiptRequiredByAnalyticCoreIsFalse :
      finalTaperReceiptRequiredByAnalyticCore ≡ false

    intermediateAllowanceFactorizationRequired : Bool
    intermediateAllowanceFactorizationRequiredIsFalse :
      intermediateAllowanceFactorizationRequired ≡ false

    directCombinedFitIsOnlyFreshScalarTheoremAfterWindowPayment : Bool
    directCombinedFitIsOnlyFreshScalarTheoremAfterWindowPaymentIsTrue :
      directCombinedFitIsOnlyFreshScalarTheoremAfterWindowPayment ≡ true

    offAnalyticCoreCompiles : Bool
    offAnalyticCoreCompilesIsTrue : offAnalyticCoreCompiles ≡ true

    offAnalyticCoreInhabitedHere : Bool
    offAnalyticCoreInhabitedHereIsFalse : offAnalyticCoreInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalWindowBudgetDirectCombinedOffCoreBoundary :
  WindowBudgetDirectCombinedOffCoreBoundary
canonicalWindowBudgetDirectCombinedOffCoreBoundary =
  window-budget-direct-combined-off-core-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "After a SelectedFiniteNearBudgetPayment exists on the exact target window, use its WindowBudgetTransportAttachment to generate the chosen-cutoff near upper mechanically. Then the only fresh scalar theorem on this concrete Off-core route is B_near(J)+B_far(J)<=A_off. Crossing-cutoff identity and same-final-taper identity remain downstream representation attachments; intermediate epsilon factorization is optional rather than mandatory. This compiles to OffAnalyticCore but does not inhabit the input or derive RH."
