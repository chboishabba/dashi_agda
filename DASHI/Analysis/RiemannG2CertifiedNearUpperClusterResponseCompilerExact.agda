module DASHI.Analysis.RiemannG2CertifiedNearUpperClusterResponseCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Order
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as Cluster
import DASHI.Analysis.RiemannG2FinalNearIndexedLiteralModelCompilerExact as Literal
import DASHI.Analysis.RiemannG2FinalCarrierFiniteSumCertificateExact as FinalCert

------------------------------------------------------------------------
-- CERTIFIED FINAL-NEAR UPPER -> DIRECT CLUSTER-RESPONSE PAYMENT
--
-- A proof-carrying finite upper certificate is useful only after its order is
-- attached to the final NearFar order.  Once attached, monotonicity compiles
--
--   nearResponse(J) <= U
--
-- into
--
--   B_complement <= cast(U + B_far(J)) + cast(D_Gamma).
--
-- The only remaining strict producer theorem is then
--
--   cast(U + B_far(J)) + cast(D_Gamma) < ClusterResponse.
--
-- This theorem remains independent of the downstream cluster=Off+Gamma balance.
------------------------------------------------------------------------

record CertifiedNearUpperOrderAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    {finiteInput}
    (kernel : Literal.FinalNearIndexedLiteralKernel offInput finiteInput)
    {certificate : FinalCert.FinalCarrierFiniteSumCertificate offInput kernel}
    (upper : FinalCert.FinalCarrierFiniteSumUpper offInput kernel certificate) : Set₁ where
  field
    certifiedOrderToNearFarOrder :
      {x y : NearFar.Scalar S} ->
      Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual
        (FinalCert.upperCertificate upper) x y ->
      NearFar._≤_ S x y

    orderAttachmentReference : String

open CertifiedNearUpperOrderAttachment public

certifiedNearUpperInSourceOrder :
  forall {S transport offInput finiteInput kernel certificate upper} ->
  CertifiedNearUpperOrderAttachment
    {S = S} {transport = transport} offInput
    {finiteInput = finiteInput} kernel
    {certificate = certificate} upper ->
  NearFar._≤_ S
    (Transport.nearResponseAt transport (Direct.chosenCutoff offInput))
    (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
      (FinalCert.upperCertificate upper))
certifiedNearUpperInSourceOrder attachment =
  certifiedOrderToNearFarOrder attachment
    (FinalCert.certifiedFinalNearBelowUpper _)

------------------------------------------------------------------------
-- Per-target strict certificate margin.
------------------------------------------------------------------------

record CertifiedNearUpperClusterMargin
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    {finiteInput}
    (kernel : Literal.FinalNearIndexedLiteralKernel
      (Direct.offInput targets) finiteInput)
    {certificate : FinalCert.FinalCarrierFiniteSumCertificate
      (Direct.offInput targets) kernel}
    (upper : FinalCert.FinalCarrierFiniteSumUpper
      (Direct.offInput targets) kernel certificate)
    (orderAttachment : CertifiedNearUpperOrderAttachment
      (Direct.offInput targets) kernel upper)
    (context : Cluster.BalanceFreeClusterResponseContext targets) : Set₁ where
  private
    offInput = Direct.offInput targets
    gamma = Direct.directGammaTarget targets
    U = Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
      (FinalCert.upperCertificate upper)
  field
    certifiedEnvelopeStrictBelowCluster :
      Order._<_ (Split.order (Cluster.surface context))
        (Split.add (Cluster.surface context)
          (Existing.cast (Cluster.offScalarIdentity context)
            (NearFar.add S U
              (Transport.farBudgetAt transport
                (Direct.chosenCutoff offInput))))
          (Existing.cast (Cluster.gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (Cluster.clusterScalarIdentity context)
          (Cluster.ClusterResponse context
            (Cluster.clusterUniversalPoleQuotientTaper context)))

    marginReference : String

open CertifiedNearUpperClusterMargin public

------------------------------------------------------------------------
-- Existing monotonicity compiles the certified envelope to the canonical
-- complement budget.
------------------------------------------------------------------------

sourceOffBudgetBelowCertifiedEnvelope :
  forall {S transport targets finiteInput kernel certificate upper orderAttachment} ->
  NearFar._≤_ S
    (Direct.directOffBudget (Direct.offInput targets)
      (Transport.universalPoleQuotientTaper transport))
    (NearFar.add S
      (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
        (FinalCert.upperCertificate upper))
      (Transport.farBudgetAt transport
        (Direct.chosenCutoff (Direct.offInput targets))))
sourceOffBudgetBelowCertifiedEnvelope
    {S = S} {targets = targets} {orderAttachment = orderAttachment} =
  NearFar.addMonotone S
    (certifiedNearUpperInSourceOrder orderAttachment)
    (Direct.sourceOrderReflexive (Direct.offInput targets)
      (Transport.farBudgetAt _
        (Direct.chosenCutoff (Direct.offInput targets))))

compiledComplementBudgetBelowCertifiedEnvelope :
  forall {S transport targets finiteInput kernel certificate upper orderAttachment context} ->
  let gamma = Direct.directGammaTarget targets
      U = Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
        (FinalCert.upperCertificate upper)
  in Order._≤_ (Split.order (Cluster.surface context))
      (Split.add (Cluster.surface context)
        (Existing.cast (Cluster.offScalarIdentity context)
          (Off.OffOrdinateBudget (Direct.directOffTarget targets)
            (Off.universalPoleQuotientTaper (Direct.directOffTarget targets))))
        (Existing.cast (Cluster.gammaScalarIdentity context)
          (Gamma.GammaBudget gamma
            (Gamma.universalPoleQuotientTaper gamma))))
      (Split.add (Cluster.surface context)
        (Existing.cast (Cluster.offScalarIdentity context)
          (NearFar.add S U
            (Transport.farBudgetAt transport
              (Direct.chosenCutoff (Direct.offInput targets)))))
        (Existing.cast (Cluster.gammaScalarIdentity context)
          (Gamma.GammaBudget gamma
            (Gamma.universalPoleQuotientTaper gamma))))
compiledComplementBudgetBelowCertifiedEnvelope
    {S = S} {targets = targets} {orderAttachment = orderAttachment}
    {context = context} =
  Split.addMonotone (Cluster.surface context)
    (Cluster.offOrderTransport context
      (sourceOffBudgetBelowCertifiedEnvelope
        {S = S} {targets = targets} {orderAttachment = orderAttachment}))
    (Cluster.compiledGammaUpper context)

compileCertifiedUpperToDirectClusterPayment :
  forall {S transport targets finiteInput kernel certificate upper orderAttachment context} ->
  CertifiedNearUpperClusterMargin
    {S = S} {transport = transport} targets
    {finiteInput = finiteInput} kernel
    {certificate = certificate} upper orderAttachment context ->
  Cluster.DirectClusterResponsePayment context
compileCertifiedUpperToDirectClusterPayment
    {context = context} margin = record
  { Cluster.complementBudgetStrictBelowClusterResponse =
      Order.leLtTrans (Split.order (Cluster.surface context))
        (compiledComplementBudgetBelowCertifiedEnvelope)
        (certifiedEnvelopeStrictBelowCluster margin)
  ; Cluster.paymentReference = marginReference margin
  }

record CertifiedNearUpperClusterBoundary : Set where
  constructor certified-near-upper-cluster-boundary
  field
    finiteUpperCertificateCanFeedCanonicalHighPayment : Bool
    finiteUpperCertificateCanFeedCanonicalHighPaymentIsTrue :
      finiteUpperCertificateCanFeedCanonicalHighPayment ≡ true

    selectedWeilWindowRequired : Bool
    selectedWeilWindowRequiredIsFalse : selectedWeilWindowRequired ≡ false

    determinantConsumerRequired : Bool
    determinantConsumerRequiredIsFalse : determinantConsumerRequired ≡ false

    finalBalanceAvailableToCertifiedMargin : Bool
    finalBalanceAvailableToCertifiedMarginIsFalse :
      finalBalanceAvailableToCertifiedMargin ≡ false

    strictCertifiedEnvelopeBelowClusterStillRequired : Bool
    strictCertifiedEnvelopeBelowClusterStillRequiredIsTrue :
      strictCertifiedEnvelopeBelowClusterStillRequired ≡ true

    finiteCertificateAloneProvesRH : Bool
    finiteCertificateAloneProvesRHIsFalse : finiteCertificateAloneProvesRH ≡ false

    highestAlphaReading : String

canonicalCertifiedNearUpperClusterBoundary : CertifiedNearUpperClusterBoundary
canonicalCertifiedNearUpperClusterBoundary =
  certified-near-upper-cluster-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    "A proof-carrying upper certificate on the exact final near sum is a valid computational producer once its order is attached to the NearFar order. Monotonicity then compiles near<=U into the canonical complement budget. The remaining theorem is the independent strict certificate margin cast(U+B_far)+cast(D_Gamma)<ClusterResponse. No selected Weil window, determinant consumer, or downstream final balance is used to prove that margin. The certificate alone does not prove RH."
