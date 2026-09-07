module DASHI.Analysis.RiemannG2AllowancePaymentsToAnalyticCoresExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact as Certified

------------------------------------------------------------------------
-- TERMINAL PAYMENT -> MINIMAL ANALYTIC CORE FACTORIZATION
--
-- The newer analytic-core API is strictly a factorization of the historical
-- terminal payment records into theorem-bearing analysis plus representation
-- attachment.  This owner makes that factorization generic: every existing
-- producer of a final Off/Gamma payment can be consumed by the preferred core
-- route without rebuilding its proof.
------------------------------------------------------------------------

offPaymentToAnalyticCore :
  Payment.PoleQuotientOffAllowancePayment → Core.OffAnalyticCore
offPaymentToAnalyticCore payment = record
  { Core.target = Payment.PoleQuotientOffAllowancePayment.target payment
  ; Core.assignedOffAllowance = Payment.assignedOffAllowance payment
  ; Core.offBudgetBelowAssignedAllowance =
      Payment.offBudgetBelowAssignedAllowance payment
  ; Core.analyticReference = Payment.producerReference payment
  }

offPaymentToRepresentationAttachment :
  (payment : Payment.PoleQuotientOffAllowancePayment) →
  Core.OffRepresentationAttachment (offPaymentToAnalyticCore payment)
offPaymentToRepresentationAttachment payment = record
  { Core.crossingCutoffFeedsThisExactOffProducer =
      Payment.crossingCutoffFeedsThisExactOffProducer payment
  ; Core.crossingCutoffFeedsThisExactOffProducerReceipt =
      Payment.crossingCutoffFeedsThisExactOffProducerReceipt payment
  ; Core.sameLiteralPoleQuotientTaperAsFinalConsumer =
      Payment.PoleQuotientOffAllowancePayment.sameLiteralPoleQuotientTaperAsFinalConsumer payment
  ; Core.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      Payment.PoleQuotientOffAllowancePayment.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt payment
  ; Core.attachmentReference = Payment.producerReference payment
  }

gammaPaymentToAnalyticCore :
  Payment.PoleQuotientGammaAllowancePayment → Core.GammaAnalyticCore
gammaPaymentToAnalyticCore payment = record
  { Core.target = Payment.PoleQuotientGammaAllowancePayment.target payment
  ; Core.assignedGammaAllowance = Payment.assignedGammaAllowance payment
  ; Core.gammaBudgetBelowAssignedAllowance =
      Payment.gammaBudgetBelowAssignedAllowance payment
  ; Core.analyticReference = Payment.PoleQuotientGammaAllowancePayment.producerReference payment
  }

gammaPaymentToRepresentationAttachment :
  (payment : Payment.PoleQuotientGammaAllowancePayment) →
  Core.GammaRepresentationAttachment (gammaPaymentToAnalyticCore payment)
gammaPaymentToRepresentationAttachment payment = record
  { Core.sameLiteralPoleQuotientTaperAsFinalConsumer =
      Payment.PoleQuotientGammaAllowancePayment.sameLiteralPoleQuotientTaperAsFinalConsumer payment
  ; Core.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      Payment.PoleQuotientGammaAllowancePayment.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt payment
  ; Core.attachmentReference = Payment.PoleQuotientGammaAllowancePayment.producerReference payment
  }

------------------------------------------------------------------------
-- Round trips: the preferred core compiler returns the same payment fields.
------------------------------------------------------------------------

offPaymentRoundTrip :
  (payment : Payment.PoleQuotientOffAllowancePayment) →
  Core.compileOffAllowancePayment
    (offPaymentToAnalyticCore payment)
    (offPaymentToRepresentationAttachment payment)
  ≡ payment
offPaymentRoundTrip payment = refl

gammaPaymentRoundTrip :
  (payment : Payment.PoleQuotientGammaAllowancePayment) →
  Core.compileGammaAllowancePayment
    (gammaPaymentToAnalyticCore payment)
    (gammaPaymentToRepresentationAttachment payment)
  ≡ payment
gammaPaymentRoundTrip payment = refl

------------------------------------------------------------------------
-- Concrete highest-alpha consequence for the new certified finite-near route.
--
-- A proof-carrying finite-near certificate plus the already-separated transport,
-- far-fit and slack receipts already compiles a terminal Off payment. Therefore
-- it also compiles the minimal OffAnalyticCore. The remaining search obligation
-- is inhabitance of that finite packet; there is no additional analytic-core
-- theorem between the packet and the preferred terminal API.
------------------------------------------------------------------------

certifiedFiniteNearUpperToOffAnalyticCore :
  ∀ {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {window : Window.PoleNearTargetWindow space formula}
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S} →
  Certified.CertifiedFiniteNearUpperOffPacket space formula window S transport →
  Core.OffAnalyticCore
certifiedFiniteNearUpperToOffAnalyticCore packet =
  offPaymentToAnalyticCore
    (Certified.compileCertifiedFiniteNearUpperOffPayment packet)

certifiedFiniteNearUpperToOffAttachment :
  ∀ {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {window : Window.PoleNearTargetWindow space formula}
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S} →
  (packet : Certified.CertifiedFiniteNearUpperOffPacket space formula window S transport) →
  Core.OffRepresentationAttachment
    (certifiedFiniteNearUpperToOffAnalyticCore packet)
certifiedFiniteNearUpperToOffAttachment packet =
  offPaymentToRepresentationAttachment
    (Certified.compileCertifiedFiniteNearUpperOffPayment packet)

certifiedFiniteNearUpperCorePaymentRoundTrip :
  ∀ {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {window : Window.PoleNearTargetWindow space formula}
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S} →
  (packet : Certified.CertifiedFiniteNearUpperOffPacket space formula window S transport) →
  Core.compileOffAllowancePayment
    (certifiedFiniteNearUpperToOffAnalyticCore packet)
    (certifiedFiniteNearUpperToOffAttachment packet)
  ≡ Certified.compileCertifiedFiniteNearUpperOffPayment packet
certifiedFiniteNearUpperCorePaymentRoundTrip packet = refl

record AllowancePaymentCoreFactorizationBoundary : Set where
  constructor allowance-payment-core-factorization-boundary
  field
    existingTerminalPaymentNeedsNewAnalysisToBecomeCore : Bool
    existingTerminalPaymentNeedsNewAnalysisToBecomeCoreIsFalse :
      existingTerminalPaymentNeedsNewAnalysisToBecomeCore ≡ false

    paymentRepresentationReceiptsArePartOfCoreMathematics : Bool
    paymentRepresentationReceiptsArePartOfCoreMathematicsIsFalse :
      paymentRepresentationReceiptsArePartOfCoreMathematics ≡ false

    paymentCoreRoundTripIsExact : Bool
    paymentCoreRoundTripIsExactIsTrue : paymentCoreRoundTripIsExact ≡ true

    certifiedFiniteNearRouteReachesMinimalOffCore : Bool
    certifiedFiniteNearRouteReachesMinimalOffCoreIsTrue :
      certifiedFiniteNearRouteReachesMinimalOffCore ≡ true

    certifiedFiniteNearPacketInhabitedHere : Bool
    certifiedFiniteNearPacketInhabitedHereIsFalse :
      certifiedFiniteNearPacketInhabitedHere ≡ false

    gammaCoreInhabitedHere : Bool
    gammaCoreInhabitedHereIsFalse : gammaCoreInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalAllowancePaymentCoreFactorizationBoundary :
  AllowancePaymentCoreFactorizationBoundary
canonicalAllowancePaymentCoreFactorizationBoundary =
  allowance-payment-core-factorization-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
