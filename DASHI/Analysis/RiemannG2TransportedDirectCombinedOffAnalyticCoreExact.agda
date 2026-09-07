module DASHI.Analysis.RiemannG2TransportedDirectCombinedOffAnalyticCoreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannG2TransportedChosenCutoffDirectCombinedAllowanceExact as PaymentRoute
import DASHI.Analysis.RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact as Factored

------------------------------------------------------------------------
-- LEAST-PRIVILEGE OFF ANALYTIC CORE
--
-- OffAnalyticCore contains only the final Off target and the theorem that its
-- budget fits the assigned allowance.  Crossing-cutoff identity and literal
-- final-taper identity are representation attachments downstream of the core.
-- Therefore they must not be primitive hypotheses of a producer whose output is
-- only OffAnalyticCore.
------------------------------------------------------------------------

record DirectCombinedTransportedOffCoreInput
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    chosenCutoff : Transport.Cutoff transport

    nearUpperAtChosen : Transport.FiniteNearUpperAt transport chosenCutoff

    assignedOffAllowance : NearFar.Scalar S

    chosenCombinedBudgetBelowAssigned :
      NearFar._≤_ S
        (NearFar.add S
          (Transport.nearBudgetAt transport chosenCutoff)
          (Transport.farBudgetAt transport chosenCutoff))
        assignedOffAllowance

    analyticReference : String

open DirectCombinedTransportedOffCoreInput public

chosenNearFarBudget :
  forall {S transport} ->
  DirectCombinedTransportedOffCoreInput S transport ->
  NearFar.NearFarOffOrdinateBudget S
chosenNearFarBudget {transport = transport} input =
  Transport.compileNearFarBudgetAt
    transport
    (chosenCutoff input)
    (nearUpperAtChosen input)

chosenOffBudget :
  forall {S transport} ->
  DirectCombinedTransportedOffCoreInput S transport ->
  Transport.Taper transport ->
  NearFar.Scalar S
chosenOffBudget {S = S} {transport = transport} input taper =
  NearFar.add S
    (Transport.nearBudgetAt transport (chosenCutoff input))
    (Transport.farBudgetAt transport (chosenCutoff input))

compileOffTarget :
  forall {S transport} ->
  DirectCombinedTransportedOffCoreInput S transport ->
  Off.PoleQuotientOffOrdinateBudgetTarget
compileOffTarget {S = S} {transport = transport} input =
  Off.pole-quotient-off-ordinate-budget-target
    (NearFar.Scalar S)
    (Transport.Taper transport)
    (Transport.fullResponse transport)
    (chosenOffBudget input)
    (NearFar._≤_ S)
    (Transport.universalPoleQuotientTaper transport)
    (NearFar.compiledOffOrdinateUpper (chosenNearFarBudget input))

compileOffAnalyticCore :
  forall {S transport} ->
  DirectCombinedTransportedOffCoreInput S transport ->
  Core.OffAnalyticCore
compileOffAnalyticCore input =
  Core.off-analytic-core
    (compileOffTarget input)
    (assignedOffAllowance input)
    (chosenCombinedBudgetBelowAssigned input)
    (analyticReference input)

------------------------------------------------------------------------
-- STRONGER PAYMENT-SHAPED ROUTES PROJECT TO THE SMALLER CORE INPUT
------------------------------------------------------------------------

fromDirectPaymentRoute :
  forall {S transport} ->
  PaymentRoute.DirectCombinedTransportedOffAllowanceInput S transport ->
  DirectCombinedTransportedOffCoreInput S transport
fromDirectPaymentRoute input = record
  { chosenCutoff = PaymentRoute.chosenCutoff input
  ; nearUpperAtChosen = PaymentRoute.nearUpperAtChosen input
  ; assignedOffAllowance = PaymentRoute.assignedOffAllowance input
  ; chosenCombinedBudgetBelowAssigned =
      PaymentRoute.chosenCombinedBudgetBelowAssigned input
  ; analyticReference = PaymentRoute.producerReference input
  }

fromFactoredRoute :
  forall {S transport} ->
  Factored.TransportedChosenCutoffOffAllowanceInput S transport ->
  DirectCombinedTransportedOffCoreInput S transport
fromFactoredRoute input = record
  { chosenCutoff = Factored.chosenCutoff input
  ; nearUpperAtChosen = Factored.nearUpperAtChosen input
  ; assignedOffAllowance = Factored.assignedOffAllowance input
  ; chosenCombinedBudgetBelowAssigned =
      Factored.chosenCombinedBudgetBelowAssigned input
  ; analyticReference = Factored.producerReference input
  }

factoredRouteCompilesOffAnalyticCore :
  forall {S transport} ->
  Factored.TransportedChosenCutoffOffAllowanceInput S transport ->
  Core.OffAnalyticCore
factoredRouteCompilesOffAnalyticCore input =
  compileOffAnalyticCore (fromFactoredRoute input)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record DirectCombinedTransportedOffCoreBoundary : Set where
  constructor direct-combined-transported-off-core-boundary
  field
    crossingCutoffPredicateRequiredToConstructAnalyticCore : Bool
    crossingCutoffPredicateRequiredToConstructAnalyticCoreIsFalse :
      crossingCutoffPredicateRequiredToConstructAnalyticCore ≡ false

    crossingCutoffReceiptRequiredToConstructAnalyticCore : Bool
    crossingCutoffReceiptRequiredToConstructAnalyticCoreIsFalse :
      crossingCutoffReceiptRequiredToConstructAnalyticCore ≡ false

    sameFinalTaperReceiptRequiredToConstructAnalyticCore : Bool
    sameFinalTaperReceiptRequiredToConstructAnalyticCoreIsFalse :
      sameFinalTaperReceiptRequiredToConstructAnalyticCore ≡ false

    intermediateFarAllowanceRequiredToConstructAnalyticCore : Bool
    intermediateFarAllowanceRequiredToConstructAnalyticCoreIsFalse :
      intermediateFarAllowanceRequiredToConstructAnalyticCore ≡ false

    chosenTransportedNearUpperStillRequired : Bool
    chosenTransportedNearUpperStillRequiredIsTrue :
      chosenTransportedNearUpperStillRequired ≡ true

    directCombinedBudgetFitStillRequired : Bool
    directCombinedBudgetFitStillRequiredIsTrue :
      directCombinedBudgetFitStillRequired ≡ true

    representationReceiptsRemainRequiredDownstream : Bool
    representationReceiptsRemainRequiredDownstreamIsTrue :
      representationReceiptsRemainRequiredDownstream ≡ true

    strongerPaymentRoutesProjectToCore : Bool
    strongerPaymentRoutesProjectToCoreIsTrue :
      strongerPaymentRoutesProjectToCore ≡ true

    offAnalyticCoreInhabitedHere : Bool
    offAnalyticCoreInhabitedHereIsFalse : offAnalyticCoreInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalDirectCombinedTransportedOffCoreBoundary :
  DirectCombinedTransportedOffCoreBoundary
canonicalDirectCombinedTransportedOffCoreBoundary =
  direct-combined-transported-off-core-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "For the primitive OffAnalyticCore consumer, choose one transported cutoff J, prove its finite-near upper, and prove the literal combined budget fit B_near(J)+B_far(J)<=A_off. Those data construct the exact Off target and analytic core directly. Crossing-cutoff identity and same-final-taper identity are representation receipts and therefore remain downstream attachments rather than analytic-core hypotheses. Intermediate epsilon factorization is also unnecessary. Stronger payment-shaped routes project to this core input. No core inhabitant or RH theorem is fabricated here."
