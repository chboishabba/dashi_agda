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
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal
import DASHI.Analysis.RiemannG2FinalCarrierFiniteSumCertificateExact as FinalCert
import DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact as Concrete

record CertifiedNearUpperOrderAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (kernel : Literal.FinalNearLiteralKernel offInput)
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
  forall {S transport offInput kernel certificate upper} ->
  CertifiedNearUpperOrderAttachment
    {S = S} {transport = transport} offInput kernel
    {certificate = certificate} upper ->
  NearFar._≤_ S
    (Transport.nearResponseAt transport (Direct.chosenCutoff offInput))
    (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
      (FinalCert.upperCertificate upper))
certifiedNearUpperInSourceOrder attachment =
  certifiedOrderToNearFarOrder attachment
    (FinalCert.certifiedFinalNearBelowUpper _)

record CertifiedNearUpperClusterMargin
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    (kernel : Literal.FinalNearLiteralKernel (Direct.offInput targets))
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

sourceOffBudgetBelowCertifiedEnvelope :
  forall {S transport targets kernel certificate upper orderAttachment} ->
  NearFar._≤_ S
    (Direct.directOffBudget (Direct.offInput targets)
      (Transport.universalPoleQuotientTaper transport))
    (NearFar.add S
      (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
        (FinalCert.upperCertificate upper))
      (Transport.farBudgetAt transport
        (Direct.chosenCutoff (Direct.offInput targets))))
sourceOffBudgetBelowCertifiedEnvelope
    {S = S} {transport = transport} {targets = targets}
    {orderAttachment = orderAttachment} =
  NearFar.addMonotone S
    (certifiedNearUpperInSourceOrder orderAttachment)
    (Direct.sourceOrderReflexive (Direct.offInput targets)
      (Transport.farBudgetAt transport
        (Direct.chosenCutoff (Direct.offInput targets))))

compiledComplementBudgetBelowCertifiedEnvelope :
  forall {S transport targets kernel certificate upper orderAttachment context} ->
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
  forall {S transport targets kernel certificate upper orderAttachment context} ->
  CertifiedNearUpperClusterMargin
    {S = S} {transport = transport} targets kernel
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

------------------------------------------------------------------------
-- CONCRETE CERTIFICATE CARRIER ROUTE
------------------------------------------------------------------------

record ConcreteCertifiedNearUpperClusterMargin
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    {carrier : Cert.FiniteAdditiveCarrier}
    {certificate : Cert.ProofCarryingFiniteSumEnclosure carrier}
    (bridge : Concrete.ConcreteCertificateFinalScalarBridge
      (Direct.offInput targets) carrier certificate)
    (upperBridge : Concrete.ConcreteCertificateFinalUpperBridge bridge)
    (context : Cluster.BalanceFreeClusterResponseContext targets) : Set₁ where
  private
    offInput = Direct.offInput targets
    gamma = Direct.directGammaTarget targets
    sourceUpper = Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
      (Concrete.upperCertificate upperBridge)
    finalUpper = Concrete.embed bridge sourceUpper
  field
    concreteCertifiedEnvelopeStrictBelowCluster :
      Order._<_ (Split.order (Cluster.surface context))
        (Split.add (Cluster.surface context)
          (Existing.cast (Cluster.offScalarIdentity context)
            (NearFar.add S finalUpper
              (Transport.farBudgetAt transport
                (Direct.chosenCutoff offInput))))
          (Existing.cast (Cluster.gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (Cluster.clusterScalarIdentity context)
          (Cluster.ClusterResponse context
            (Cluster.clusterUniversalPoleQuotientTaper context)))
    concreteMarginReference : String

open ConcreteCertifiedNearUpperClusterMargin public

concreteSourceOffBudgetBelowCertifiedEnvelope :
  forall {S transport targets carrier certificate bridge upperBridge} ->
  NearFar._≤_ S
    (Direct.directOffBudget (Direct.offInput targets)
      (Transport.universalPoleQuotientTaper transport))
    (NearFar.add S
      (Concrete.embed bridge
        (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
          (Concrete.upperCertificate upperBridge)))
      (Transport.farBudgetAt transport
        (Direct.chosenCutoff (Direct.offInput targets))))
concreteSourceOffBudgetBelowCertifiedEnvelope
    {S = S} {transport = transport} {targets = targets}
    {upperBridge = upperBridge} =
  NearFar.addMonotone S
    (Concrete.compiledFinalNearBelowEmbeddedUpper upperBridge)
    (Direct.sourceOrderReflexive (Direct.offInput targets)
      (Transport.farBudgetAt transport
        (Direct.chosenCutoff (Direct.offInput targets))))

compiledComplementBudgetBelowConcreteCertifiedEnvelope :
  forall {S transport targets carrier certificate bridge upperBridge context} ->
  let gamma = Direct.directGammaTarget targets
      U = Concrete.embed bridge
        (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
          (Concrete.upperCertificate upperBridge))
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
compiledComplementBudgetBelowConcreteCertifiedEnvelope
    {S = S} {targets = targets} {bridge = bridge}
    {upperBridge = upperBridge} {context = context} =
  Split.addMonotone (Cluster.surface context)
    (Cluster.offOrderTransport context
      (concreteSourceOffBudgetBelowCertifiedEnvelope
        {S = S} {targets = targets} {bridge = bridge}
        {upperBridge = upperBridge}))
    (Cluster.compiledGammaUpper context)

compileConcreteCertifiedUpperToDirectClusterPayment :
  forall {S transport targets carrier certificate bridge upperBridge context} ->
  ConcreteCertifiedNearUpperClusterMargin
    {S = S} {transport = transport} targets
    {carrier = carrier} {certificate = certificate}
    bridge upperBridge context ->
  Cluster.DirectClusterResponsePayment context
compileConcreteCertifiedUpperToDirectClusterPayment
    {context = context} margin = record
  { Cluster.complementBudgetStrictBelowClusterResponse =
      Order.leLtTrans (Split.order (Cluster.surface context))
        (compiledComplementBudgetBelowConcreteCertifiedEnvelope)
        (concreteCertifiedEnvelopeStrictBelowCluster margin)
  ; Cluster.paymentReference = concreteMarginReference margin
  }

record CertifiedNearUpperClusterBoundary : Set where
  constructor certified-near-upper-cluster-boundary
  field
    evaluatorIndexedKernelRequired : Bool
    evaluatorIndexedKernelRequiredIsFalse : evaluatorIndexedKernelRequired ≡ false
    finiteUpperCertificateCanFeedCanonicalHighPayment : Bool
    finiteUpperCertificateCanFeedCanonicalHighPaymentIsTrue :
      finiteUpperCertificateCanFeedCanonicalHighPayment ≡ true
    certificateScalarMustEqualFinalScalar : Bool
    certificateScalarMustEqualFinalScalarIsFalse :
      certificateScalarMustEqualFinalScalar ≡ false
    concreteCertificateBridgeFeedsCanonicalHighPayment : Bool
    concreteCertificateBridgeFeedsCanonicalHighPaymentIsTrue :
      concreteCertificateBridgeFeedsCanonicalHighPayment ≡ true
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
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    "The computational route need not identify its concrete certificate scalar definitionally with the final analytic scalar. Either use the legacy final-scalar certificate route, or keep an exact rational/interval backend concrete and supply one embedded-fold equality plus one upper-order transport. Both compile to B_off <= U+B_far and then the same balance-free strict ClusterResponse payment. Certification alone still does not prove the strict margin or RH."
