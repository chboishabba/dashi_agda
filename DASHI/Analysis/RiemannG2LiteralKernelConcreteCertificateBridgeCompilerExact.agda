module DASHI.Analysis.RiemannG2LiteralKernelConcreteCertificateBridgeCompilerExact where

------------------------------------------------------------------------
-- LITERAL R1 KERNEL -> CONCRETE CERTIFICATE BRIDGE
--
-- Once the final literal kernel exists, the concrete-certificate bridge needs
-- only one additional same-object weld:
--
--   finiteNearSum(cellResponse) = embed(certifiedFold).
--
-- The final nearResponse equality is then obtained by transitivity from the
-- literal kernel.  This prevents the optional certificate path from demanding
-- a second independent nearResponseAt representation theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal
import DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact as Concrete

record LiteralKernelCertifiedFoldWeld
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    {offInput : Direct.DirectLiteralOffTargetInput S transport}
    {carrier : Cert.FiniteAdditiveCarrier}
    {certificate : Cert.ProofCarryingFiniteSumEnclosure carrier}
    (kernel : Literal.FinalNearLiteralKernel offInput)
    : Set₁ where
  field
    embed :
      Cert.Scalar carrier → NearFar.Scalar S

    literalFiniteFoldIsEmbeddedCertifiedFold :
      Literal.finiteNearSum kernel (Literal.cellResponse kernel)
      ≡
      embed
        (Cert.foldScalars carrier
          (Cert.mapValues
            (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
            (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)))

    weldReference : String

open LiteralKernelCertifiedFoldWeld public

compileConcreteCertificateFinalScalarBridge :
  ∀ {S transport offInput carrier certificate}
    (kernel : Literal.FinalNearLiteralKernel
      {S = S} {transport = transport} offInput) →
  (weld : LiteralKernelCertifiedFoldWeld
    {S = S} {transport = transport}
    {offInput = offInput}
    {carrier = carrier} {certificate = certificate}
    kernel) →
  Concrete.ConcreteCertificateFinalScalarBridge
    offInput carrier certificate
compileConcreteCertificateFinalScalarBridge kernel weld = record
  { Concrete.embed = embed weld
  ; Concrete.finalNearIsEmbeddedCertifiedFold =
      trans
        (Literal.finalNearResponseIsLiteralFiniteSum kernel)
        (literalFiniteFoldIsEmbeddedCertifiedFold weld)
  ; Concrete.bridgeReference = weldReference weld
  }

record LiteralKernelCertificateBridgeBoundary : Set where
  constructor literal-kernel-certificate-bridge-boundary
  field
    secondIndependentNearResponseRepresentationNeededForCertificateRoute : Bool
    literalKernelEqualityReused : Bool
    certificateRouteStillNeedsLiteralFoldToCertifiedFoldWeld : Bool
    literalKernelInhabitedHere : Bool
    certifiedFoldWeldInhabitedHere : Bool
    rhDerived : Bool

open LiteralKernelCertificateBridgeBoundary public

canonicalLiteralKernelCertificateBridgeBoundary :
  LiteralKernelCertificateBridgeBoundary
canonicalLiteralKernelCertificateBridgeBoundary =
  literal-kernel-certificate-bridge-boundary
    false true true false false false
