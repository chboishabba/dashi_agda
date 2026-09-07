module DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact where

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
import DASHI.Analysis.RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact as Off
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment

------------------------------------------------------------------------
-- CERTIFIED FINITE NEAR -> FINAL OFF PAYMENT
------------------------------------------------------------------------

record CertifiedFiniteNearOffPacket
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    certified : Certified.CertifiedSelectedFiniteNearEvaluation space formula window
    certifiedBudget : Certified.CertifiedSelectedFiniteNearBudgetInput certified

    chosenCutoff : Transport.Cutoff transport

    windowTransport :
      WindowTransport.WindowBudgetTransportAttachment
        space
        formula
        window
        (Certified.compileSelectedFiniteNearBudgetPayment certified certifiedBudget)
        S
        transport
        chosenCutoff

    CrossingCutoff : Transport.Cutoff transport → Set
    chosenCutoffCrosses : CrossingCutoff chosenCutoff

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

open CertifiedFiniteNearOffPacket public

compiledSelectedPayment :
  ∀ {space formula window S transport} →
  (packet : CertifiedFiniteNearOffPacket space formula window S transport) →
  Minimal.SelectedFiniteNearBudgetPayment space formula window
compiledSelectedPayment packet =
  Certified.compileSelectedFiniteNearBudgetPayment
    (certified packet)
    (certifiedBudget packet)

compiledFiniteNearUpperAt :
  ∀ {space formula window S transport} →
  (packet : CertifiedFiniteNearOffPacket space formula window S transport) →
  Transport.FiniteNearUpperAt transport (chosenCutoff packet)
compiledFiniteNearUpperAt packet =
  WindowTransport.compileFiniteNearUpperAt (windowTransport packet)

compileChosenCutoffOffInput :
  ∀ {space formula window S transport} →
  (packet : CertifiedFiniteNearOffPacket space formula window S transport) →
  Off.TransportedChosenCutoffOffAllowanceInput S transport
compileChosenCutoffOffInput packet = record
  { Off.chosenCutoff = chosenCutoff packet
  ; Off.CrossingCutoff = CrossingCutoff packet
  ; Off.chosenCutoffCrosses = chosenCutoffCrosses packet
  ; Off.nearUpperAtChosen = compiledFiniteNearUpperAt packet
  ; Off.intermediateFarAllowance = intermediateFarAllowance packet
  ; Off.nearBudgetSelfOrder = nearBudgetSelfOrder packet
  ; Off.farBudgetBelowIntermediateAllowance =
      farBudgetBelowIntermediateAllowance packet
  ; Off.assignedOffAllowance = assignedOffAllowance packet
  ; Off.nearBudgetPlusIntermediateBelowAssigned =
      nearBudgetPlusIntermediateBelowAssigned packet
  ; Off.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameLiteralPoleQuotientTaperAsFinalConsumer packet
  ; Off.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameLiteralPoleQuotientTaperAsFinalConsumerReceipt packet
  ; Off.producerReference = producerReference packet
  }

compileCertifiedFiniteNearOffPayment :
  ∀ {space formula window S transport} →
  CertifiedFiniteNearOffPacket space formula window S transport →
  Payment.PoleQuotientOffAllowancePayment
compileCertifiedFiniteNearOffPayment packet =
  Off.compileFinalOffAllowancePayment
    (compileChosenCutoffOffInput packet)

------------------------------------------------------------------------
-- ORDERED-UPPER CERTIFICATE -> FINAL OFF PAYMENT
--
-- Stronger preferred route.  The finite certificate already carries its exact
-- upper endpoint, so no second arbitrary analytic budget predicate is supplied.
------------------------------------------------------------------------

record CertifiedFiniteNearUpperOffPacket
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (window : Window.PoleNearTargetWindow space formula)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : Transport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    certified : Certified.CertifiedSelectedFiniteNearEvaluation space formula window
    certifiedUpper : Certified.CertifiedSelectedFiniteNearUpperInput certified

    chosenCutoff : Transport.Cutoff transport

    windowTransport :
      WindowTransport.WindowBudgetTransportAttachment
        space
        formula
        window
        (Certified.compileUpperSelectedFiniteNearBudgetPayment certified certifiedUpper)
        S
        transport
        chosenCutoff

    CrossingCutoff : Transport.Cutoff transport → Set
    chosenCutoffCrosses : CrossingCutoff chosenCutoff

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

open CertifiedFiniteNearUpperOffPacket public

compiledUpperSelectedPayment :
  ∀ {space formula window S transport} →
  (packet : CertifiedFiniteNearUpperOffPacket space formula window S transport) →
  Minimal.SelectedFiniteNearBudgetPayment space formula window
compiledUpperSelectedPayment packet =
  Certified.compileUpperSelectedFiniteNearBudgetPayment
    (CertifiedFiniteNearUpperOffPacket.certified packet)
    (CertifiedFiniteNearUpperOffPacket.certifiedUpper packet)

compiledUpperFiniteNearUpperAt :
  ∀ {space formula window S transport} →
  (packet : CertifiedFiniteNearUpperOffPacket space formula window S transport) →
  Transport.FiniteNearUpperAt transport
    (CertifiedFiniteNearUpperOffPacket.chosenCutoff packet)
compiledUpperFiniteNearUpperAt packet =
  WindowTransport.compileFiniteNearUpperAt
    (CertifiedFiniteNearUpperOffPacket.windowTransport packet)

compileUpperChosenCutoffOffInput :
  ∀ {space formula window S transport} →
  (packet : CertifiedFiniteNearUpperOffPacket space formula window S transport) →
  Off.TransportedChosenCutoffOffAllowanceInput S transport
compileUpperChosenCutoffOffInput packet = record
  { Off.chosenCutoff = CertifiedFiniteNearUpperOffPacket.chosenCutoff packet
  ; Off.CrossingCutoff = CertifiedFiniteNearUpperOffPacket.CrossingCutoff packet
  ; Off.chosenCutoffCrosses =
      CertifiedFiniteNearUpperOffPacket.chosenCutoffCrosses packet
  ; Off.nearUpperAtChosen = compiledUpperFiniteNearUpperAt packet
  ; Off.intermediateFarAllowance =
      CertifiedFiniteNearUpperOffPacket.intermediateFarAllowance packet
  ; Off.nearBudgetSelfOrder =
      CertifiedFiniteNearUpperOffPacket.nearBudgetSelfOrder packet
  ; Off.farBudgetBelowIntermediateAllowance =
      CertifiedFiniteNearUpperOffPacket.farBudgetBelowIntermediateAllowance packet
  ; Off.assignedOffAllowance =
      CertifiedFiniteNearUpperOffPacket.assignedOffAllowance packet
  ; Off.nearBudgetPlusIntermediateBelowAssigned =
      CertifiedFiniteNearUpperOffPacket.nearBudgetPlusIntermediateBelowAssigned packet
  ; Off.sameLiteralPoleQuotientTaperAsFinalConsumer =
      CertifiedFiniteNearUpperOffPacket.sameLiteralPoleQuotientTaperAsFinalConsumer packet
  ; Off.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      CertifiedFiniteNearUpperOffPacket.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt packet
  ; Off.producerReference = CertifiedFiniteNearUpperOffPacket.producerReference packet
  }

compileCertifiedFiniteNearUpperOffPayment :
  ∀ {space formula window S transport} →
  CertifiedFiniteNearUpperOffPacket space formula window S transport →
  Payment.PoleQuotientOffAllowancePayment
compileCertifiedFiniteNearUpperOffPayment packet =
  Off.compileFinalOffAllowancePayment
    (compileUpperChosenCutoffOffInput packet)

record CertifiedFiniteNearOffBoundary : Set where
  constructor certified-finite-near-off-boundary
  field
    secondFiniteEvaluationAfterCertificate : Bool
    secondFiniteEvaluationAfterCertificateIsFalse :
      secondFiniteEvaluationAfterCertificate ≡ false

    allCutoffNearFamilyRequired : Bool
    allCutoffNearFamilyRequiredIsFalse : allCutoffNearFamilyRequired ≡ false

    crossProverSplitFarTransportStillRequired : Bool
    crossProverSplitFarTransportStillRequiredIsTrue :
      crossProverSplitFarTransportStillRequired ≡ true

    sameChosenCutoffFarFitStillRequired : Bool
    sameChosenCutoffFarFitStillRequiredIsTrue :
      sameChosenCutoffFarFitStillRequired ≡ true

    selectedNearSlackStillRequired : Bool
    selectedNearSlackStillRequiredIsTrue :
      selectedNearSlackStillRequired ≡ true

    finiteCertificateRouteCompilesTerminalOffPayment : Bool
    finiteCertificateRouteCompilesTerminalOffPaymentIsTrue :
      finiteCertificateRouteCompilesTerminalOffPayment ≡ true

    offPaymentInhabitedHere : Bool
    offPaymentInhabitedHereIsFalse : offPaymentInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalCertifiedFiniteNearOffBoundary : CertifiedFiniteNearOffBoundary
canonicalCertifiedFiniteNearOffBoundary =
  certified-finite-near-off-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

record CertifiedFiniteNearUpperOffBoundary : Set where
  constructor certified-finite-near-upper-off-boundary
  field
    arbitrarySecondNearUpperPredicateRequired : Bool
    arbitrarySecondNearUpperPredicateRequiredIsFalse :
      arbitrarySecondNearUpperPredicateRequired ≡ false

    certifiedUpperEndpointCompilesTerminalOffPayment : Bool
    certifiedUpperEndpointCompilesTerminalOffPaymentIsTrue :
      certifiedUpperEndpointCompilesTerminalOffPayment ≡ true

    selectedWindowOrderTransportStillRequired : Bool
    selectedWindowOrderTransportStillRequiredIsTrue :
      selectedWindowOrderTransportStillRequired ≡ true

    farFitAndNearSlackStillRequired : Bool
    farFitAndNearSlackStillRequiredIsTrue :
      farFitAndNearSlackStillRequired ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalCertifiedFiniteNearUpperOffBoundary :
  CertifiedFiniteNearUpperOffBoundary
canonicalCertifiedFiniteNearUpperOffBoundary =
  certified-finite-near-upper-off-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
