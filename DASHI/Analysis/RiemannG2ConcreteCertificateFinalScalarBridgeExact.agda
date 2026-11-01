module DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact where

------------------------------------------------------------------------
-- CONCRETE CERTIFICATE CARRIER -> FINAL RH SCALAR
--
-- The canonical final Near/Far scalar is intentionally abstract.  A machine-
-- checkable finite certificate therefore must not be forced to use that scalar
-- definitionally.  The least-privilege bridge is instead:
--
--   concrete certificate fold
--          | exact same-object embedding theorem
--          v
--   final nearResponseAt(J)
--
-- together with one transport of the certificate's ordered upper relation into
-- the final Near/Far order.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct

record ConcreteCertificateFinalScalarBridge
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (carrier : Cert.FiniteAdditiveCarrier)
    (certificate : Cert.ProofCarryingFiniteSumEnclosure carrier) : Set₁ where
  private
    finalScalar = NearFar.Scalar S
    sourceScalar = Cert.Scalar carrier
  field
    embed : sourceScalar -> finalScalar

    finalNearIsEmbeddedCertifiedFold :
      Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
      ≡
      embed
        (Cert.foldScalars carrier
          (Cert.mapValues
            (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
            (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)))

    bridgeReference : String

open ConcreteCertificateFinalScalarBridge public

record ConcreteCertificateFinalUpperBridge
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {carrier : Cert.FiniteAdditiveCarrier}
    {certificate : Cert.ProofCarryingFiniteSumEnclosure carrier}
    (bridge : ConcreteCertificateFinalScalarBridge offInput carrier certificate)
    : Set₁ where
  field
    upperCertificate :
      Cert.ProofCarryingFiniteSumUpperEnclosure carrier certificate

    sourceUpperTransport :
      forall {x y : Cert.Scalar carrier} ->
      Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual
        upperCertificate x y ->
      NearFar._≤_ S (embed bridge x) (embed bridge y)

    upperReference : String

open ConcreteCertificateFinalUpperBridge public

compiledFinalNearBelowEmbeddedUpper :
  forall {S transport offInput carrier certificate bridge} ->
  (upper : ConcreteCertificateFinalUpperBridge
    {S = S} {transport = transport}
    {offInput = offInput}
    {carrier = carrier} {certificate = certificate}
    bridge) ->
  NearFar._≤_ S
    (Transport.nearResponseAt transport (Direct.chosenCutoff offInput))
    (embed bridge
      (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
        (upperCertificate upper)))
compiledFinalNearBelowEmbeddedUpper {carrier = carrier} {certificate = certificate}
  {bridge = bridge} upper
  with finalNearIsEmbeddedCertifiedFold bridge
... | refl =
  sourceUpperTransport upper
    (Cert.finiteSumBelowCertifiedUpper (upperCertificate upper))

record ConcreteCertificateFinalScalarBoundary : Set where
  constructor concrete-certificate-final-scalar-boundary
  field
    certificateScalarMustDefinitionallyEqualFinalAnalyticScalar : Bool
    certificateScalarMustDefinitionallyEqualFinalAnalyticScalarIsFalse :
      certificateScalarMustDefinitionallyEqualFinalAnalyticScalar ≡ false

    exactEmbeddedFoldIdentityStillRequired : Bool
    exactEmbeddedFoldIdentityStillRequiredIsTrue :
      exactEmbeddedFoldIdentityStillRequired ≡ true

    oneCertificateOrderTransportStillRequired : Bool
    oneCertificateOrderTransportStillRequiredIsTrue :
      oneCertificateOrderTransportStillRequired ≡ true

    rationalCertificateBackendMayRemainConcrete : Bool
    rationalCertificateBackendMayRemainConcreteIsTrue :
      rationalCertificateBackendMayRemainConcrete ≡ true

    concreteCertificateAloneProvesStrictClusterResponseMargin : Bool
    concreteCertificateAloneProvesStrictClusterResponseMarginIsFalse :
      concreteCertificateAloneProvesStrictClusterResponseMargin ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalConcreteCertificateFinalScalarBoundary :
  ConcreteCertificateFinalScalarBoundary
canonicalConcreteCertificateFinalScalarBoundary =
  concrete-certificate-final-scalar-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Do not require a machine certificate scalar to be definitionally equal to the final analytic NearFar scalar. Keep the certificate backend concrete (for example exact rational/interval arithmetic), provide one proof-relevant embedding of the certified fold into final nearResponseAt(J), and transport the certified upper relation once. This removes an unnecessary concrete-real quotient prerequisite while preserving the genuine same-object representation theorem and the independent strict ClusterResponse margin."
