module DASHI.Analysis.RiemannG2ConcreteCertificateLiteralEnumerationExact where

------------------------------------------------------------------------
-- CONCRETE CERTIFICATE TERMS -> LITERAL FINAL-NEAR ENUMERATION
--
-- `FinalNearLiteralKernel.finiteNearSum` is intentionally abstract.  A machine
-- certificate needs one additional representation layer before its concrete
-- list fold can be identified with that literal finite sum.
--
-- This owner makes that layer local and proof-relevant:
--
--   * enumerate the literal zero indices as a List;
--   * map every certificate term to its literal zero index;
--   * prove that embedding preserves zero/addition on the used carrier;
--   * prove every embedded certificate term is the corresponding literal cell;
--   * prove the kernel's abstract finiteNearSum is the fold over that exact list.
--
-- The embedded whole-fold equality is then compiler output by induction.  No RH
-- analytic inequality is introduced here.
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
import DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact as Bridge

finalFold :
  forall {S transport offInput} ->
  (kernel : Literal.FinalNearLiteralKernel
    {S = S} {transport = transport} offInput) ->
  NearFar.Scalar S ->
  List (Literal.ZeroIndex kernel) ->
  NearFar.Scalar S
finalFold {S = S} kernel zero [] = zero
finalFold {S = S} kernel zero (i ∷ is) =
  NearFar.add S
    (Literal.cellResponse kernel i)
    (finalFold kernel zero is)

record ConcreteCertificateLiteralEnumeration
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport)
    (kernel : Literal.FinalNearLiteralKernel offInput)
    (carrier : Cert.FiniteAdditiveCarrier)
    (certificate : Cert.ProofCarryingFiniteSumEnclosure carrier) : Set₁ where
  field
    embed : Cert.Scalar carrier -> NearFar.Scalar S
    finalZero : NearFar.Scalar S

    literalIndices : List (Literal.ZeroIndex kernel)
    certificateTermIndex :
      Cert.ProofCarryingFiniteSumEnclosure.Term certificate ->
      Literal.ZeroIndex kernel

    certificateTermsEnumerateLiteralIndices :
      Cert.mapValues certificateTermIndex
        (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)
      ≡ literalIndices

    sourceZeroEmbedsFinalZero :
      embed (Cert.zeroS carrier) ≡ finalZero

    embedAdd :
      (x y : Cert.Scalar carrier) ->
      embed (Cert.addS carrier x y)
      ≡ NearFar.add S (embed x) (embed y)

    embeddedTermIsLiteralCell :
      (term : Cert.ProofCarryingFiniteSumEnclosure.Term certificate) ->
      embed (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate term)
      ≡ Literal.cellResponse kernel (certificateTermIndex term)

    literalFiniteSumIsEnumeratedFold :
      Literal.finiteNearSum kernel (Literal.cellResponse kernel)
      ≡ finalFold kernel finalZero literalIndices

    enumerationReference : String

open ConcreteCertificateLiteralEnumeration public

embeddedFoldMatchesMappedTerms :
  forall {S transport offInput kernel carrier certificate} ->
  (enumeration : ConcreteCertificateLiteralEnumeration
    {S = S} {transport = transport}
    offInput kernel carrier certificate) ->
  (terms : List (Cert.ProofCarryingFiniteSumEnclosure.Term certificate)) ->
  embed enumeration (Cert.foldScalars carrier
    (Cert.mapValues
      (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
      terms))
  ≡ finalFold kernel (finalZero enumeration)
      (Cert.mapValues (certificateTermIndex enumeration) terms)
embeddedFoldMatchesMappedTerms enumeration [] =
  sourceZeroEmbedsFinalZero enumeration
embeddedFoldMatchesMappedTerms {S = S} {kernel = kernel}
    {carrier = carrier} {certificate = certificate}
    enumeration (term ∷ terms)
  rewrite embedAdd enumeration
    (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate term)
    (Cert.foldScalars carrier
      (Cert.mapValues
        (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
        terms))
        | embeddedTermIsLiteralCell enumeration term
        | embeddedFoldMatchesMappedTerms enumeration terms = refl

embeddedCertificateFoldIsLiteralFiniteSum :
  forall {S transport offInput kernel carrier certificate} ->
  (enumeration : ConcreteCertificateLiteralEnumeration
    {S = S} {transport = transport}
    offInput kernel carrier certificate) ->
  embed enumeration
    (Cert.foldScalars carrier
      (Cert.mapValues
        (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
        (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)))
  ≡ Literal.finiteNearSum kernel (Literal.cellResponse kernel)
embeddedCertificateFoldIsLiteralFiniteSum
    {kernel = kernel} {certificate = certificate} enumeration =
  trans
    (embeddedFoldMatchesMappedTerms enumeration
      (Cert.ProofCarryingFiniteSumEnclosure.terms certificate))
    (trans
      (cong (finalFold kernel (finalZero enumeration))
        (certificateTermsEnumerateLiteralIndices enumeration))
      (sym (literalFiniteSumIsEnumeratedFold enumeration)))

compileLiteralFoldAttachment :
  forall {S transport offInput kernel carrier certificate} ->
  (enumeration : ConcreteCertificateLiteralEnumeration
    {S = S} {transport = transport}
    offInput kernel carrier certificate) ->
  Bridge.ConcreteCertificateLiteralFoldAttachment
    offInput kernel carrier certificate
compileLiteralFoldAttachment enumeration = record
  { Bridge.embedLiteralFold = embed enumeration
  ; Bridge.embeddedCertifiedFoldIsLiteralFiniteSum =
      embeddedCertificateFoldIsLiteralFiniteSum enumeration
  ; Bridge.attachmentReference = enumerationReference enumeration
  }

record ConcreteCertificateLiteralEnumerationBoundary : Set where
  constructor concrete-certificate-literal-enumeration-boundary
  field
    monolithicEmbeddedFoldEqualityPrimitive : Bool
    monolithicEmbeddedFoldEqualityPrimitiveIsFalse :
      monolithicEmbeddedFoldEqualityPrimitive ≡ false

    exactLiteralIndexEnumerationRequired : Bool
    exactLiteralIndexEnumerationRequiredIsTrue :
      exactLiteralIndexEnumerationRequired ≡ true

    termwiseCellIdentityRequired : Bool
    termwiseCellIdentityRequiredIsTrue :
      termwiseCellIdentityRequired ≡ true

    localZeroAndAddEmbeddingRequired : Bool
    localZeroAndAddEmbeddingRequiredIsTrue :
      localZeroAndAddEmbeddingRequired ≡ true

    abstractFiniteNearSumToListFoldRequired : Bool
    abstractFiniteNearSumToListFoldRequiredIsTrue :
      abstractFiniteNearSumToListFoldRequired ≡ true

    embeddedWholeFoldIsCompilerOutput : Bool
    embeddedWholeFoldIsCompilerOutputIsTrue :
      embeddedWholeFoldIsCompilerOutput ≡ true

    strictClusterResponseMarginPaidHere : Bool
    strictClusterResponseMarginPaidHereIsFalse :
      strictClusterResponseMarginPaidHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalConcreteCertificateLiteralEnumerationBoundary :
  ConcreteCertificateLiteralEnumerationBoundary
canonicalConcreteCertificateLiteralEnumerationBoundary =
  concrete-certificate-literal-enumeration-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "For an executable finite certificate, expose the literal nearOffFinset enumeration rather than treating finiteNearSum as an opaque scalar operation. Align certificate terms with that list, prove termwise embedded values equal the literal reflection-paired cells, preserve zero/addition locally, and identify the kernel finiteNearSum with the exact enumerated fold. The whole embedded certificate fold equality is then induction/compiler output. This is representation debt only; it does not pay the strict ClusterResponse theorem or RH."
