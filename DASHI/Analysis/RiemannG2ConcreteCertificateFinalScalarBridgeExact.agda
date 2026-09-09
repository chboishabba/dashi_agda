module DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact where

------------------------------------------------------------------------
-- CONCRETE CERTIFICATE CARRIER -> FINAL RH SCALAR
--
-- A machine-checkable certificate may live on a concrete scalar distinct from
-- the final analytic Near/Far scalar.  Least privilege is:
--
--   R1: final nearResponseAt(J) = literal finite near sum
--   C0: embed(concrete certified fold) = that same literal finite near sum
--
-- then equality transitivity compiles
--
--   final nearResponseAt(J) = embed(concrete certified fold).
--
-- One order transport then moves the proof-carrying certified upper into the
-- final Near/Far order.  No whole-scalar equality or quotient realization is
-- required.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal

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

------------------------------------------------------------------------
-- R1-FACTORED CONSTRUCTION OF THE BRIDGE
------------------------------------------------------------------------

record ConcreteCertificateLiteralFoldAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (kernel : Literal.FinalNearLiteralKernel offInput)
    (carrier : Cert.FiniteAdditiveCarrier)
    (certificate : Cert.ProofCarryingFiniteSumEnclosure carrier) : Set₁ where
  private
    finalScalar = NearFar.Scalar S
    sourceScalar = Cert.Scalar carrier
  field
    embedLiteralFold : sourceScalar -> finalScalar

    embeddedCertifiedFoldIsLiteralFiniteSum :
      embedLiteralFold
        (Cert.foldScalars carrier
          (Cert.mapValues
            (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
            (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)))
      ≡ Literal.finiteNearSum kernel (Literal.cellResponse kernel)

    attachmentReference : String

open ConcreteCertificateLiteralFoldAttachment public

compileConcreteCertificateFinalScalarBridge :
  forall {S transport offInput kernel carrier certificate} ->
  ConcreteCertificateLiteralFoldAttachment
    {S = S} {transport = transport}
    offInput kernel carrier certificate ->
  ConcreteCertificateFinalScalarBridge offInput carrier certificate
compileConcreteCertificateFinalScalarBridge {kernel = kernel} attachment = record
  { embed = embedLiteralFold attachment
  ; finalNearIsEmbeddedCertifiedFold =
      trans
        (Literal.finalNearResponseIsLiteralFiniteSum kernel)
        (sym (embeddedCertifiedFoldIsLiteralFiniteSum attachment))
  ; bridgeReference = attachmentReference attachment
  }
  where
  sym : forall {A : Set} {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  trans : forall {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl yz = yz

------------------------------------------------------------------------
-- CERTIFIED UPPER TRANSPORT
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- FRONTIER / FIREWALLS
------------------------------------------------------------------------

record ConcreteCertificateFinalScalarBoundary : Set where
  constructor concrete-certificate-final-scalar-boundary
  field
    certificateScalarMustDefinitionallyEqualFinalAnalyticScalar : Bool
    certificateScalarMustDefinitionallyEqualFinalAnalyticScalarIsFalse :
      certificateScalarMustDefinitionallyEqualFinalAnalyticScalar ≡ false

    independentSecondFinalNearIdentityRequiredAfterR1 : Bool
    independentSecondFinalNearIdentityRequiredAfterR1IsFalse :
      independentSecondFinalNearIdentityRequiredAfterR1 ≡ false

    embeddedConcreteFoldToLiteralSumStillRequired : Bool
    embeddedConcreteFoldToLiteralSumStillRequiredIsTrue :
      embeddedConcreteFoldToLiteralSumStillRequired ≡ true

    oneCertificateOrderTransportStillRequired : Bool
    oneCertificateOrderTransportStillRequiredIsTrue :
      oneCertificateOrderTransportStillRequired ≡ true

    rationalCertificateBackendMayRemainConcrete : Bool
    rationalCertificateBackendMayRemainConcreteIsTrue :
      rationalCertificateBackendMayRemainConcrete ≡ true

    r1PlusEmbeddedFoldCompilesFinalBridge : Bool
    r1PlusEmbeddedFoldCompilesFinalBridgeIsTrue :
      r1PlusEmbeddedFoldCompilesFinalBridge ≡ true

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
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Keep the certificate backend concrete and distinct from the final analytic scalar. Do not require a second independent theorem saying final nearResponseAt(J)=embed(certifiedFold): reuse canonical R1, final nearResponseAt(J)=literal finite sum, and prove only that the embedded concrete certified fold is that same literal sum. Equality transitivity compiles the final bridge. One source-upper order transport is still required, and the strict ClusterResponse margin remains independent mathematics."
