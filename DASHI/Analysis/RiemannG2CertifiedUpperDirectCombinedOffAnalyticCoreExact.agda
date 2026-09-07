module DASHI.Analysis.RiemannG2CertifiedUpperDirectCombinedOffAnalyticCoreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2CertifiedFiniteNearEvaluationCompilerExact as Certified
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as Minimal
import DASHI.Analysis.RiemannG2WindowBudgetToTransportedNearUpperExact as WindowTransport
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2TransportedDirectCombinedOffAnalyticCoreExact as DirectCore
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

------------------------------------------------------------------------
-- PROOF-CARRYING FINITE UPPER + DIRECT COMBINED FIT -> OFF ANALYTIC CORE
--
-- This is the least-privilege concrete Off route currently exposed in-repo.
-- A proof-carrying finite upper certificate compiles to the minimal selected
-- target-window payment.  The existing exact window/order attachment compiles
-- that payment to the one transported near upper at J.  The direct-combined
-- core compiler then needs only
--
--   B_near(J) + B_far(J) <= A_off.
--
-- In particular this route does not pass through the older
-- DirectFinitePoleNearProducer / DirectSignedConsumerPayment determinant-side
-- consumer, and it does not require crossing/final-taper representation receipts
-- merely to construct OffAnalyticCore.
------------------------------------------------------------------------

record CertifiedUpperDirectCombinedOffCoreInput
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    certified :
      Certified.CertifiedSelectedFiniteNearEvaluation space formula window

    certifiedUpper :
      Certified.CertifiedSelectedFiniteNearUpperInput certified

    chosenCutoff : Transport.Cutoff transport

    windowTransport :
      WindowTransport.WindowBudgetTransportAttachment
        space
        formula
        window
        (Certified.compileUpperSelectedFiniteNearBudgetPayment
          certified certifiedUpper)
        S
        transport
        chosenCutoff

    assignedOffAllowance : NearFar.Scalar S

    chosenCombinedBudgetBelowAssigned :
      NearFar._≤_ S
        (NearFar.add S
          (Transport.nearBudgetAt transport chosenCutoff)
          (Transport.farBudgetAt transport chosenCutoff))
        assignedOffAllowance

    analyticReference : String

open CertifiedUpperDirectCombinedOffCoreInput public

compiledSelectedFiniteNearPayment :
  forall {space formula window S transport} ->
  (input :
    CertifiedUpperDirectCombinedOffCoreInput
      space formula window S transport) ->
  Minimal.SelectedFiniteNearBudgetPayment space formula window
compiledSelectedFiniteNearPayment input =
  Certified.compileUpperSelectedFiniteNearBudgetPayment
    (certified input)
    (certifiedUpper input)

compiledFiniteNearUpperAt :
  forall {space formula window S transport} ->
  (input :
    CertifiedUpperDirectCombinedOffCoreInput
      space formula window S transport) ->
  Transport.FiniteNearUpperAt transport (chosenCutoff input)
compiledFiniteNearUpperAt input =
  WindowTransport.compileFiniteNearUpperAt (windowTransport input)

compileDirectCombinedCoreInput :
  forall {space formula window S transport} ->
  CertifiedUpperDirectCombinedOffCoreInput
    space formula window S transport ->
  DirectCore.DirectCombinedTransportedOffCoreInput S transport
compileDirectCombinedCoreInput input = record
  { DirectCore.chosenCutoff = chosenCutoff input
  ; DirectCore.nearUpperAtChosen = compiledFiniteNearUpperAt input
  ; DirectCore.assignedOffAllowance = assignedOffAllowance input
  ; DirectCore.chosenCombinedBudgetBelowAssigned =
      chosenCombinedBudgetBelowAssigned input
  ; DirectCore.analyticReference = analyticReference input
  }

compileOffAnalyticCore :
  forall {space formula window S transport} ->
  CertifiedUpperDirectCombinedOffCoreInput
    space formula window S transport ->
  Core.OffAnalyticCore
compileOffAnalyticCore input =
  DirectCore.compileOffAnalyticCore
    (compileDirectCombinedCoreInput input)

------------------------------------------------------------------------
-- BOUNDARY / PROOF-SEARCH CLASSIFICATION
------------------------------------------------------------------------

record CertifiedUpperDirectCombinedOffCoreBoundary : Set where
  constructor certified-upper-direct-combined-off-core-boundary
  field
    determinantDirectSignedConsumerPaymentRequired : Bool
    determinantDirectSignedConsumerPaymentRequiredIsFalse :
      determinantDirectSignedConsumerPaymentRequired ≡ false

    secondFiniteEvaluationRequired : Bool
    secondFiniteEvaluationRequiredIsFalse :
      secondFiniteEvaluationRequired ≡ false

    secondAnalyticNearUpperReceiptRequired : Bool
    secondAnalyticNearUpperReceiptRequiredIsFalse :
      secondAnalyticNearUpperReceiptRequired ≡ false

    crossingCutoffReceiptRequiredForAnalyticCore : Bool
    crossingCutoffReceiptRequiredForAnalyticCoreIsFalse :
      crossingCutoffReceiptRequiredForAnalyticCore ≡ false

    sameFinalTaperReceiptRequiredForAnalyticCore : Bool
    sameFinalTaperReceiptRequiredForAnalyticCoreIsFalse :
      sameFinalTaperReceiptRequiredForAnalyticCore ≡ false

    intermediateFarAllowanceRequired : Bool
    intermediateFarAllowanceRequiredIsFalse :
      intermediateFarAllowanceRequired ≡ false

    exactCertifiedFoldIdentityStillRequired : Bool
    exactCertifiedFoldIdentityStillRequiredIsTrue :
      exactCertifiedFoldIdentityStillRequired ≡ true

    exactSelectedWindowTransportStillRequired : Bool
    exactSelectedWindowTransportStillRequiredIsTrue :
      exactSelectedWindowTransportStillRequired ≡ true

    directCombinedBudgetFitStillRequired : Bool
    directCombinedBudgetFitStillRequiredIsTrue :
      directCombinedBudgetFitStillRequired ≡ true

    certifiedUpperAndCombinedFitCompileOffCore : Bool
    certifiedUpperAndCombinedFitCompileOffCoreIsTrue :
      certifiedUpperAndCombinedFitCompileOffCore ≡ true

    offAnalyticCoreInhabitedHere : Bool
    offAnalyticCoreInhabitedHereIsFalse :
      offAnalyticCoreInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCertifiedUpperDirectCombinedOffCoreBoundary :
  CertifiedUpperDirectCombinedOffCoreBoundary
canonicalCertifiedUpperDirectCombinedOffCoreBoundary =
  certified-upper-direct-combined-off-core-boundary
    false refl
    false refl
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
    "The concrete determinant-free Off route is: proof-carrying finite-sum upper enclosure with exact fold identity to the selected pole-near window; one exact window/value/budget/order transport to the selected cutoff; then the single literal theorem B_near(J)+B_far(J)<=A_off. These compile directly to OffAnalyticCore. The older DirectSignedConsumerPayment, a second finite evaluation, a second near-upper proof, intermediate epsilon decomposition, crossing receipt and final-taper receipt are not analytic-core prerequisites. Representation receipts remain downstream. No Off core inhabitant or RH theorem is fabricated here."
