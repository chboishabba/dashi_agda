module DASHI.Core.OddGrassmannCoefficientGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- One-generator odd Grassmann coefficient gate.
--
-- This module keeps the candidate surface explicit: a body coefficient,
-- an odd coefficient, the expansion a + bθ, the [θ]f extractor, and the
-- one-generator odd derivative / Berezin integral all collapse to the same
-- receipt-projected string surface.

record OddGrassmannCoefficientGateReceipt : Set where
  constructor mkOddGrassmannCoefficientGateReceipt
  field
    payloadLabel :
      String

    payloadOwner :
      String

    payloadSurface :
      String

    generator :
      String

    body :
      String

    oddCoefficient :
      String

    expansion :
      String

    thetaCoefficientLabel :
      String

    thetaCoefficientExtractorSurface :
      String

    oddDerivativeSurface :
      String

    berezinIntegralSurface :
      String

    residualWitness :
      String

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    semanticAuthority :
      Bool

    semanticAuthorityIsFalse :
      semanticAuthority ≡ false

    measureAuthority :
      Bool

    measureAuthorityIsFalse :
      measureAuthority ≡ false

    variationAuthority :
      Bool

    variationAuthorityIsFalse :
      variationAuthority ≡ false

    proofAuthority :
      Bool

    proofAuthorityIsFalse :
      proofAuthority ≡ false

open OddGrassmannCoefficientGateReceipt public

------------------------------------------------------------------------
-- Canonical receipt.

canonicalOddGrassmannCoefficientGateReceipt :
  OddGrassmannCoefficientGateReceipt
canonicalOddGrassmannCoefficientGateReceipt =
  mkOddGrassmannCoefficientGateReceipt
    "odd grassmann coefficient gate"
    "candidate-only"
    "one-generator odd lane"
    "theta"
    "a"
    "b"
    "a + bθ"
    "[θ]f"
    "b"
    "b"
    "b"
    "b"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Collapsed one-generator surfaces.

thetaCoefficientExtractor :
  OddGrassmannCoefficientGateReceipt →
  String
thetaCoefficientExtractor receipt =
  oddCoefficient receipt

oddDerivative :
  OddGrassmannCoefficientGateReceipt →
  String
oddDerivative receipt =
  oddCoefficient receipt

berezinIntegral :
  OddGrassmannCoefficientGateReceipt →
  String
berezinIntegral receipt =
  oddCoefficient receipt

oddDerivativeSurfaceExtractor :
  OddGrassmannCoefficientGateReceipt →
  String
oddDerivativeSurfaceExtractor receipt =
  oddDerivativeSurface receipt

berezinIntegralSurfaceExtractor :
  OddGrassmannCoefficientGateReceipt →
  String
berezinIntegralSurfaceExtractor receipt =
  berezinIntegralSurface receipt

------------------------------------------------------------------------
-- Projection lemmas for the canonical receipt.

canonicalPayloadLabelIsCanonical :
  payloadLabel canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "odd grassmann coefficient gate"
canonicalPayloadLabelIsCanonical =
  refl

canonicalPayloadOwnerIsCanonical :
  payloadOwner canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "candidate-only"
canonicalPayloadOwnerIsCanonical =
  refl

canonicalPayloadSurfaceIsCanonical :
  payloadSurface canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "one-generator odd lane"
canonicalPayloadSurfaceIsCanonical =
  refl

canonicalGeneratorIsTheta :
  generator canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "theta"
canonicalGeneratorIsTheta =
  refl

canonicalBodyIsA :
  body canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "a"
canonicalBodyIsA =
  refl

canonicalOddCoefficientIsB :
  oddCoefficient canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "b"
canonicalOddCoefficientIsB =
  refl

canonicalExpansionIsABTheta :
  expansion canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "a + bθ"
canonicalExpansionIsABTheta =
  refl

canonicalThetaCoefficientLabelIsCanonical :
  thetaCoefficientLabel canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "[θ]f"
canonicalThetaCoefficientLabelIsCanonical =
  refl

canonicalThetaCoefficientExtractorIsCanonical :
  thetaCoefficientExtractorSurface canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "b"
canonicalThetaCoefficientExtractorIsCanonical =
  refl

canonicalOddDerivativeSurfaceIsCanonical :
  oddDerivativeSurface canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "b"
canonicalOddDerivativeSurfaceIsCanonical =
  refl

canonicalBerezinIntegralSurfaceIsCanonical :
  berezinIntegralSurface canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "b"
canonicalBerezinIntegralSurfaceIsCanonical =
  refl

canonicalResidualWitnessIsCanonical :
  residualWitness canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "b"
canonicalResidualWitnessIsCanonical =
  refl

canonicalCandidateOnlyIsTrue :
  candidateOnly canonicalOddGrassmannCoefficientGateReceipt
  ≡
  true
canonicalCandidateOnlyIsTrue =
  refl

canonicalPromotedIsFalse :
  promoted canonicalOddGrassmannCoefficientGateReceipt
  ≡
  false
canonicalPromotedIsFalse =
  refl

canonicalSemanticAuthorityIsFalse :
  semanticAuthority canonicalOddGrassmannCoefficientGateReceipt
  ≡
  false
canonicalSemanticAuthorityIsFalse =
  refl

canonicalMeasureAuthorityIsFalse :
  measureAuthority canonicalOddGrassmannCoefficientGateReceipt
  ≡
  false
canonicalMeasureAuthorityIsFalse =
  refl

canonicalVariationAuthorityIsFalse :
  variationAuthority canonicalOddGrassmannCoefficientGateReceipt
  ≡
  false
canonicalVariationAuthorityIsFalse =
  refl

canonicalProofAuthorityIsFalse :
  proofAuthority canonicalOddGrassmannCoefficientGateReceipt
  ≡
  false
canonicalProofAuthorityIsFalse =
  refl

------------------------------------------------------------------------
-- Collapse lemmas.

thetaCoefficientExtractorIsBodyPlusOddCoefficient :
  (receipt : OddGrassmannCoefficientGateReceipt) →
  thetaCoefficientExtractor receipt ≡ oddCoefficient receipt
thetaCoefficientExtractorIsBodyPlusOddCoefficient receipt =
  refl

canonicalThetaCoefficientLabelRecordsExtractor :
  thetaCoefficientLabel canonicalOddGrassmannCoefficientGateReceipt
  ≡
  "[θ]f"
canonicalThetaCoefficientLabelRecordsExtractor =
  refl

oddDerivativeCollapsesToThetaCoefficientExtractor :
  (receipt : OddGrassmannCoefficientGateReceipt) →
  oddDerivative receipt ≡ thetaCoefficientExtractor receipt
oddDerivativeCollapsesToThetaCoefficientExtractor receipt =
  refl

berezinIntegralCollapsesToThetaCoefficientExtractor :
  (receipt : OddGrassmannCoefficientGateReceipt) →
  berezinIntegral receipt ≡ thetaCoefficientExtractor receipt
berezinIntegralCollapsesToThetaCoefficientExtractor receipt =
  refl

oddDerivativeCollapsesToBerezinIntegral :
  (receipt : OddGrassmannCoefficientGateReceipt) →
  oddDerivative receipt ≡ berezinIntegral receipt
oddDerivativeCollapsesToBerezinIntegral receipt =
  refl

oddDerivativeSurfaceExtractorIsOddDerivativeSurface :
  (receipt : OddGrassmannCoefficientGateReceipt) →
  oddDerivativeSurfaceExtractor receipt ≡ oddDerivativeSurface receipt
oddDerivativeSurfaceExtractorIsOddDerivativeSurface receipt =
  refl

berezinIntegralSurfaceExtractorIsBerezinIntegralSurface :
  (receipt : OddGrassmannCoefficientGateReceipt) →
  berezinIntegralSurfaceExtractor receipt ≡ berezinIntegralSurface receipt
berezinIntegralSurfaceExtractorIsBerezinIntegralSurface receipt =
  refl
