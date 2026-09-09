module DASHI.Analysis.RiemannG2CertifiedClusterLowerEnvelopeCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Order
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as Cluster
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal
import DASHI.Analysis.RiemannG2FinalCarrierFiniteSumCertificateExact as FinalCert
import DASHI.Analysis.RiemannG2CertifiedNearUpperClusterResponseCompilerExact as Certified

------------------------------------------------------------------------
-- OPTIONAL PRODUCER: CERTIFIED ENVELOPE < L <= ACTUAL CLUSTER RESPONSE
--
-- The terminal consumer does not require an intermediate cluster lower L.
-- However, the checked-Lean history reports quantitative cluster-margin
-- mathematics as an existing source asset.  If that theorem is transported
-- proof-relevantly onto the SAME balance-free final carrier, we should reuse it
-- as an optional producer rather than force a new direct comparison with the
-- opaque ClusterResponse field.
--
-- This owner therefore separates:
--   (1) a theorem-bearing lower certificate L <= ClusterResponse;
--   (2) the still-independent strict certified envelope < L.
-- Their transitive composition pays the existing direct ClusterResponse
-- consumer.  Boolean/status provenance cannot construct (1).
------------------------------------------------------------------------

record CertifiedClusterLower
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    {targets : Direct.DirectLiteralComplementTargets S transport}
    (context : Cluster.BalanceFreeClusterResponseContext targets) : Set₁ where
  field
    lower : Order.Scalar (Split.order (Cluster.surface context))

    lowerBelowActualClusterResponse :
      Order._≤_ (Split.order (Cluster.surface context))
        lower
        (Existing.cast (Cluster.clusterScalarIdentity context)
          (Cluster.ClusterResponse context
            (Cluster.clusterUniversalPoleQuotientTaper context)))

    sameObjectLowerReference : String

open CertifiedClusterLower public

record CertifiedEnvelopeBelowClusterLower
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    (kernel : Literal.FinalNearLiteralKernel (Direct.offInput targets))
    {certificate : FinalCert.FinalCarrierFiniteSumCertificate
      (Direct.offInput targets) kernel}
    (upper : FinalCert.FinalCarrierFiniteSumUpper
      (Direct.offInput targets) kernel certificate)
    (orderAttachment : Certified.CertifiedNearUpperOrderAttachment
      (Direct.offInput targets) kernel upper)
    (context : Cluster.BalanceFreeClusterResponseContext targets)
    (clusterLower : CertifiedClusterLower context) : Set₁ where
  private
    offInput = Direct.offInput targets
    gamma = Direct.directGammaTarget targets
    U = Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
      (FinalCert.upperCertificate upper)
  field
    certifiedEnvelopeStrictBelowLower :
      Order._<_ (Split.order (Cluster.surface context))
        (Split.add (Cluster.surface context)
          (Existing.cast (Cluster.offScalarIdentity context)
            (NearFar.add S U
              (Transport.farBudgetAt transport
                (Direct.chosenCutoff offInput))))
          (Existing.cast (Cluster.gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (lower clusterLower)

    strictEnvelopeReference : String

open CertifiedEnvelopeBelowClusterLower public

compileClusterLowerRouteToCertifiedClusterMargin :
  forall {S transport targets kernel certificate upper orderAttachment context clusterLower} ->
  CertifiedEnvelopeBelowClusterLower
    {S = S} {transport = transport}
    targets kernel {certificate = certificate} upper orderAttachment context clusterLower ->
  Certified.CertifiedNearUpperClusterMargin
    targets kernel {certificate = certificate} upper orderAttachment context
compileClusterLowerRouteToCertifiedClusterMargin
    {context = context} {clusterLower = clusterLower} payment = record
  { Certified.certifiedEnvelopeStrictBelowCluster =
      Order.ltLeTrans (Split.order (Cluster.surface context))
        (certifiedEnvelopeStrictBelowLower payment)
        (lowerBelowActualClusterResponse clusterLower)
  ; Certified.marginReference = strictEnvelopeReference payment
  }

compileClusterLowerRouteToDirectClusterPayment :
  forall {S transport targets kernel certificate upper orderAttachment context clusterLower} ->
  CertifiedEnvelopeBelowClusterLower
    {S = S} {transport = transport}
    targets kernel {certificate = certificate} upper orderAttachment context clusterLower ->
  Cluster.DirectClusterResponsePayment context
compileClusterLowerRouteToDirectClusterPayment payment =
  Certified.compileCertifiedUpperToDirectClusterPayment
    (compileClusterLowerRouteToCertifiedClusterMargin payment)

record CertifiedClusterLowerEnvelopeBoundary : Set where
  constructor certified-cluster-lower-envelope-boundary
  field
    intermediateClusterLowerPrimitiveAtClayConsumer : Bool
    intermediateClusterLowerPrimitiveAtClayConsumerIsFalse :
      intermediateClusterLowerPrimitiveAtClayConsumer ≡ false

    theoremBearingClusterLowerIsValidOptionalProducer : Bool
    theoremBearingClusterLowerIsValidOptionalProducerIsTrue :
      theoremBearingClusterLowerIsValidOptionalProducer ≡ true

    checkedLeanStatusBooleanInhabitsClusterLower : Bool
    checkedLeanStatusBooleanInhabitsClusterLowerIsFalse :
      checkedLeanStatusBooleanInhabitsClusterLower ≡ false

    finalBalanceAvailableToStrictEnvelopeProof : Bool
    finalBalanceAvailableToStrictEnvelopeProofIsFalse :
      finalBalanceAvailableToStrictEnvelopeProof ≡ false

    clusterLowerPlusStrictEnvelopeCompilesActualClusterPayment : Bool
    clusterLowerPlusStrictEnvelopeCompilesActualClusterPaymentIsTrue :
      clusterLowerPlusStrictEnvelopeCompilesActualClusterPayment ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCertifiedClusterLowerEnvelopeBoundary :
  CertifiedClusterLowerEnvelopeBoundary
canonicalCertifiedClusterLowerEnvelopeBoundary =
  certified-cluster-lower-envelope-boundary
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    "Keep actual ClusterResponse as the terminal consumer. Optionally reuse an independently transported same-object quantitative cluster theorem as L <= ClusterResponse, then prove only the certified envelope U+B_far+D_Gamma < L. Transitivity compiles the existing direct ClusterResponse payment. The 8889 status Boolean/provenance does not inhabit the lower theorem, the final balance remains unavailable, and RH is not derived here."
