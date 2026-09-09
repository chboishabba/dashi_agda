module DASHI.Analysis.RiemannG2FinalCarrierFiniteSumCertificateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalNearIndexedLiteralModelCompilerExact as Literal

record FinalCarrierFiniteSumCertificate
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    {finiteInput}
    (kernel : Literal.FinalNearIndexedLiteralKernel offInput finiteInput) : Set₁ where
  private
    Scalar = NearFar.Scalar S
  field
    zeroS : Scalar
    addS : Scalar -> Scalar -> Scalar

    certificate :
      Cert.ProofCarryingFiniteSumEnclosure
        (record { Cert.Scalar = Scalar ; Cert.zeroS = zeroS ; Cert.addS = addS })

    certificateFoldIsLiteralFiniteSum :
      Cert.foldScalars
        (record { Cert.Scalar = Scalar ; Cert.zeroS = zeroS ; Cert.addS = addS })
        (Cert.mapValues
          (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
          (Cert.ProofCarryingFiniteSumEnclosure.terms certificate))
      ≡ Literal.finiteNearSum kernel (Literal.cellResponse kernel)

    certificateReference : String

open FinalCarrierFiniteSumCertificate public

finalCarrier :
  forall {S transport offInput finiteInput kernel} ->
  FinalCarrierFiniteSumCertificate
    {S = S} {transport = transport} offInput
    {finiteInput = finiteInput} kernel ->
  Cert.FiniteAdditiveCarrier
finalCarrier {S = S} input = record
  { Cert.Scalar = NearFar.Scalar S
  ; Cert.zeroS = zeroS input
  ; Cert.addS = addS input
  }

certifiedFoldIsFinalNearResponse :
  forall {S transport offInput finiteInput kernel} ->
  (input : FinalCarrierFiniteSumCertificate
    {S = S} {transport = transport} offInput
    {finiteInput = finiteInput} kernel) ->
  Cert.foldScalars (finalCarrier input)
    (Cert.mapValues
      (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm (certificate input))
      (Cert.ProofCarryingFiniteSumEnclosure.terms (certificate input)))
  ≡ Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
certifiedFoldIsFinalNearResponse {kernel = kernel} input =
  trans
    (certificateFoldIsLiteralFiniteSum input)
    (sym (Literal.finalNearResponseIsLiteralFiniteSum kernel))
  where
  sym : forall {A : Set} {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  trans : forall {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl yz = yz

record CertifiedFinalNearEvaluation
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    {finiteInput}
    (kernel : Literal.FinalNearIndexedLiteralKernel offInput finiteInput)
    (input : FinalCarrierFiniteSumCertificate offInput kernel) : Set₁ where
  private
    cert = certificate input
  field
    finalNearWithinApproximant :
      Cert.ProofCarryingFiniteSumEnclosure.Within cert
        (Transport.nearResponseAt transport (Direct.chosenCutoff offInput))
        (Cert.ProofCarryingFiniteSumEnclosure.approximant cert)
        (Cert.ProofCarryingFiniteSumEnclosure.error cert)

    evaluationReference : String

open CertifiedFinalNearEvaluation public

compileCertifiedFinalNearEvaluation :
  forall {S transport offInput finiteInput kernel} ->
  (input : FinalCarrierFiniteSumCertificate
    {S = S} {transport = transport} offInput
    {finiteInput = finiteInput} kernel) ->
  CertifiedFinalNearEvaluation offInput kernel input
compileCertifiedFinalNearEvaluation input
  with certifiedFoldIsFinalNearResponse input
... | refl = record
  { finalNearWithinApproximant =
      Cert.ProofCarryingFiniteSumEnclosure.finiteSumWithinApproximant
        (certificate input)
  ; evaluationReference = certificateReference input
  }

record FinalCarrierFiniteSumUpper
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    {finiteInput}
    (kernel : Literal.FinalNearIndexedLiteralKernel offInput finiteInput)
    (input : FinalCarrierFiniteSumCertificate offInput kernel) : Set₁ where
  field
    upperCertificate :
      Cert.ProofCarryingFiniteSumUpperEnclosure
        (finalCarrier input)
        (certificate input)

    upperReference : String

open FinalCarrierFiniteSumUpper public

certifiedFinalNearBelowUpper :
  forall {S transport offInput finiteInput kernel input} ->
  (upper : FinalCarrierFiniteSumUpper
    {S = S} {transport = transport} offInput
    {finiteInput = finiteInput} kernel input) ->
  Cert.ProofCarryingFiniteSumUpperEnclosure.lessOrEqual
    (upperCertificate upper)
    (Transport.nearResponseAt transport (Direct.chosenCutoff offInput))
    (Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
      (upperCertificate upper))
certifiedFinalNearBelowUpper {input = input} upper
  with certifiedFoldIsFinalNearResponse input
... | refl =
  Cert.finiteSumBelowCertifiedUpper (upperCertificate upper)

record FinalCarrierFiniteSumCertificateBoundary : Set where
  constructor final-carrier-finite-sum-certificate-boundary
  field
    selectedWeilWindowRequired : Bool
    selectedWeilWindowRequiredIsFalse : selectedWeilWindowRequired ≡ false
    determinantDirectProducerRequired : Bool
    determinantDirectProducerRequiredIsFalse : determinantDirectProducerRequired ≡ false
    exactFiniteFoldIdentityRequired : Bool
    exactFiniteFoldIdentityRequiredIsTrue : exactFiniteFoldIdentityRequired ≡ true
    genericWithinReceiptTransportsToFinalNear : Bool
    genericWithinReceiptTransportsToFinalNearIsTrue : genericWithinReceiptTransportsToFinalNear ≡ true
    orderedUpperCertificateTransportsToFinalNear : Bool
    orderedUpperCertificateTransportsToFinalNearIsTrue : orderedUpperCertificateTransportsToFinalNear ≡ true
    finiteEnumerationAloneProvesStrictClusterMargin : Bool
    finiteEnumerationAloneProvesStrictClusterMarginIsFalse : finiteEnumerationAloneProvesStrictClusterMargin ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    highestAlphaReading : String

canonicalFinalCarrierFiniteSumCertificateBoundary :
  FinalCarrierFiniteSumCertificateBoundary
canonicalFinalCarrierFiniteSumCertificateBoundary =
  final-carrier-finite-sum-certificate-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Reuse the domain-neutral ProofCarryingFiniteSumEnclosure directly on the final NearFar scalar. Once the exact certificate fold is identified with the literal final-near sum, the existing nearResponseAt(J)=literal sum theorem transports both the Within evaluation and any ordered certified upper to the actual final near response. No selected Weil window or determinant-q producer is required. Finiteness/certification alone does not prove the post-crossing strict ClusterResponse margin or RH."
