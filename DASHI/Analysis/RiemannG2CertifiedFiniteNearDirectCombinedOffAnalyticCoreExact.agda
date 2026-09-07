module DASHI.Analysis.RiemannG2CertifiedFiniteNearDirectCombinedOffAnalyticCoreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact as Certified
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as Minimal
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2WindowBudgetToTransportedNearUpperExact as WindowTransport
import DASHI.Analysis.RiemannG2WindowBudgetDirectCombinedOffAnalyticCoreExact as WindowCore
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

------------------------------------------------------------------------
-- PROOF-CARRYING FINITE UPPER CERTIFICATE
--   -> MINIMAL SELECTED-WINDOW PAYMENT
--   -> ONE SAME-OBJECT/ORDER TRANSPORT
--   -> DIRECT COMBINED OFF FIT
--   -> OFF ANALYTIC CORE
--
-- The ordered finite-sum certificate already proves its exact finite fold is
-- below a certified upper endpoint.  The certified finite-near compiler turns
-- that into the repository's minimal selected-window payment.  From there the
-- existing window transport generates the chosen-cutoff near upper.  Hence no
-- second finite-sum upper theorem and no separately manufactured near-upper
-- record are required on this route.
------------------------------------------------------------------------

record CertifiedFiniteNearDirectCombinedOffCoreInput
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (certified :
      Certified.CertifiedSelectedFiniteNearEvaluation space formula window)
    (upper : Certified.CertifiedSelectedFiniteNearUpperInput certified)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  private
    payment =
      Certified.compileUpperSelectedFiniteNearBudgetPayment certified upper
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

open CertifiedFiniteNearDirectCombinedOffCoreInput public

compiledSelectedWindowPayment :
  forall {space formula window certified upper S transport} ->
  CertifiedFiniteNearDirectCombinedOffCoreInput
    space formula window certified upper S transport ->
  Minimal.SelectedFiniteNearBudgetPayment space formula window
compiledSelectedWindowPayment {certified = certified} {upper = upper} input =
  Certified.compileUpperSelectedFiniteNearBudgetPayment certified upper

compileWindowCoreInput :
  forall {space formula window certified upper S transport} ->
  (input : CertifiedFiniteNearDirectCombinedOffCoreInput
    space formula window certified upper S transport) ->
  WindowCore.WindowBudgetDirectCombinedOffCoreInput
    space formula window
    (Certified.compileUpperSelectedFiniteNearBudgetPayment certified upper)
    S transport
compileWindowCoreInput input = record
  { WindowCore.chosenCutoff = chosenCutoff input
  ; WindowCore.windowTransport = windowTransport input
  ; WindowCore.assignedOffAllowance = assignedOffAllowance input
  ; WindowCore.chosenCombinedBudgetBelowAssigned =
      chosenCombinedBudgetBelowAssigned input
  ; WindowCore.analyticReference = analyticReference input
  }

compileOffAnalyticCore :
  forall {space formula window certified upper S transport} ->
  CertifiedFiniteNearDirectCombinedOffCoreInput
    space formula window certified upper S transport ->
  Core.OffAnalyticCore
compileOffAnalyticCore input =
  WindowCore.compileOffAnalyticCore (compileWindowCoreInput input)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record CertifiedFiniteNearDirectCombinedOffCoreBoundary : Set where
  constructor certified-finite-near-direct-combined-off-core-boundary
  field
    finiteEnumerationAloneSuffices : Bool
    finiteEnumerationAloneSufficesIsFalse :
      finiteEnumerationAloneSuffices ≡ false

    proofCarryingEnclosureRequired : Bool
    proofCarryingEnclosureRequiredIsTrue :
      proofCarryingEnclosureRequired ≡ true

    exactFoldIdentityWithSelectedWindowRequired : Bool
    exactFoldIdentityWithSelectedWindowRequiredIsTrue :
      exactFoldIdentityWithSelectedWindowRequired ≡ true

    secondFiniteSumUpperTheoremRequired : Bool
    secondFiniteSumUpperTheoremRequiredIsFalse :
      secondFiniteSumUpperTheoremRequired ≡ false

    separatelyManufacturedTransportedNearUpperRequired : Bool
    separatelyManufacturedTransportedNearUpperRequiredIsFalse :
      separatelyManufacturedTransportedNearUpperRequired ≡ false

    directCombinedOffFitStillRequired : Bool
    directCombinedOffFitStillRequiredIsTrue :
      directCombinedOffFitStillRequired ≡ true

    crossingOrFinalTaperReceiptRequiredByAnalyticCore : Bool
    crossingOrFinalTaperReceiptRequiredByAnalyticCoreIsFalse :
      crossingOrFinalTaperReceiptRequiredByAnalyticCore ≡ false

    certifiedRouteCompilesOffAnalyticCore : Bool
    certifiedRouteCompilesOffAnalyticCoreIsTrue :
      certifiedRouteCompilesOffAnalyticCore ≡ true

    offAnalyticCoreInhabitedHere : Bool
    offAnalyticCoreInhabitedHereIsFalse :
      offAnalyticCoreInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCertifiedFiniteNearDirectCombinedOffCoreBoundary :
  CertifiedFiniteNearDirectCombinedOffCoreBoundary
canonicalCertifiedFiniteNearDirectCombinedOffCoreBoundary =
  certified-finite-near-direct-combined-off-core-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "Use a proof-carrying ordered enclosure for the exact finite fold and identify that fold with window.finitePoleNearSigned. The certified compiler then produces the minimal selected-window payment without a second finite-sum upper assumption. One same-object/order transport produces the chosen-cutoff near upper mechanically. After those receipts, the only fresh scalar theorem on this sufficient Off-core route is B_near(J)+B_far(J)<=A_off. Crossing and final-taper identity remain downstream representation work. No certificate, Off core inhabitant, or RH theorem is fabricated here."
