module DASHI.Core.OddGrassmannLaneCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Odd / nilpotent lane surface.
--
-- This module keeps the principle candidate-only:
-- one odd coordinate theta, a body coefficient a, an odd coefficient b,
-- a nilpotent-law receipt string/flag, and the standard authority bits
-- remain closed.

record OddGrassmannLaneReceipt : Set where
  constructor mkOddGrassmannLaneReceipt
  field
    payloadLabel :
      String

    payloadOwner :
      String

    payloadSurface :
      String

    theta :
      String

    bodyCoeff :
      String

    oddCoeff :
      String

    residualWitness :
      String

    nilpotentLawReceipt :
      String

    nilpotentLawRecorded :
      Bool

    nilpotentLawRecordedIsTrue :
      nilpotentLawRecorded ≡ true

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

open OddGrassmannLaneReceipt public

------------------------------------------------------------------------
-- Canonical receipt.

canonicalOddGrassmannLaneReceipt :
  OddGrassmannLaneReceipt
canonicalOddGrassmannLaneReceipt =
  mkOddGrassmannLaneReceipt
    "odd grassmann lane core"
    "candidate-only"
    "theta payload"
    "theta"
    "a"
    "b"
    "b"
    "theta^2 = 0"
    true
    refl
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
-- Collapsed odd-coefficient surface.

oddCoeffExtractor :
  OddGrassmannLaneReceipt →
  String
oddCoeffExtractor receipt =
  oddCoeff receipt

differentiation :
  OddGrassmannLaneReceipt →
  String
differentiation =
  oddCoeffExtractor

integration :
  OddGrassmannLaneReceipt →
  String
integration =
  oddCoeffExtractor

probe :
  OddGrassmannLaneReceipt →
  String
probe =
  oddCoeffExtractor

measure :
  OddGrassmannLaneReceipt →
  String
measure =
  oddCoeffExtractor

oddDerivative :
  OddGrassmannLaneReceipt →
  String
oddDerivative =
  differentiation

oddIntegral :
  OddGrassmannLaneReceipt →
  String
oddIntegral =
  integration

oddProbe :
  OddGrassmannLaneReceipt →
  String
oddProbe =
  probe

oddMeasure :
  OddGrassmannLaneReceipt →
  String
oddMeasure =
  measure

nilpotentWitness :
  OddGrassmannLaneReceipt →
  String
nilpotentWitness =
  nilpotentLawReceipt

authorityGate :
  OddGrassmannLaneReceipt →
  Bool
authorityGate =
  promoted

------------------------------------------------------------------------
-- Projection lemmas for the canonical receipt.

canonicalPayloadLabelIsCanonical :
  payloadLabel canonicalOddGrassmannLaneReceipt
  ≡
  "odd grassmann lane core"
canonicalPayloadLabelIsCanonical =
  refl

canonicalPayloadOwnerIsCanonical :
  payloadOwner canonicalOddGrassmannLaneReceipt
  ≡
  "candidate-only"
canonicalPayloadOwnerIsCanonical =
  refl

canonicalPayloadSurfaceIsCanonical :
  payloadSurface canonicalOddGrassmannLaneReceipt
  ≡
  "theta payload"
canonicalPayloadSurfaceIsCanonical =
  refl

canonicalThetaIsCanonical :
  theta canonicalOddGrassmannLaneReceipt
  ≡
  "theta"
canonicalThetaIsCanonical =
  refl

canonicalBodyCoeffIsA :
  bodyCoeff canonicalOddGrassmannLaneReceipt
  ≡
  "a"
canonicalBodyCoeffIsA =
  refl

canonicalOddCoeffIsB :
  oddCoeff canonicalOddGrassmannLaneReceipt
  ≡
  "b"
canonicalOddCoeffIsB =
  refl

canonicalResidualWitnessIsB :
  residualWitness canonicalOddGrassmannLaneReceipt
  ≡
  "b"
canonicalResidualWitnessIsB =
  refl

canonicalResidualWitnessIsOddCoeff :
  residualWitness canonicalOddGrassmannLaneReceipt
  ≡
  oddCoeff canonicalOddGrassmannLaneReceipt
canonicalResidualWitnessIsOddCoeff =
  refl

canonicalNilpotentLawReceiptIsCanonical :
  nilpotentLawReceipt canonicalOddGrassmannLaneReceipt
  ≡
  "theta^2 = 0"
canonicalNilpotentLawReceiptIsCanonical =
  refl

canonicalNilpotentLawRecordedIsTrue :
  nilpotentLawRecorded canonicalOddGrassmannLaneReceipt
  ≡
  true
canonicalNilpotentLawRecordedIsTrue =
  refl

canonicalCandidateOnlyIsTrue :
  candidateOnly canonicalOddGrassmannLaneReceipt
  ≡
  true
canonicalCandidateOnlyIsTrue =
  refl

canonicalPromotedIsFalse :
  promoted canonicalOddGrassmannLaneReceipt
  ≡
  false
canonicalPromotedIsFalse =
  refl

canonicalSemanticAuthorityIsFalse :
  semanticAuthority canonicalOddGrassmannLaneReceipt
  ≡
  false
canonicalSemanticAuthorityIsFalse =
  refl

canonicalMeasureAuthorityIsFalse :
  measureAuthority canonicalOddGrassmannLaneReceipt
  ≡
  false
canonicalMeasureAuthorityIsFalse =
  refl

canonicalVariationAuthorityIsFalse :
  variationAuthority canonicalOddGrassmannLaneReceipt
  ≡
  false
canonicalVariationAuthorityIsFalse =
  refl

canonicalProofAuthorityIsFalse :
  proofAuthority canonicalOddGrassmannLaneReceipt
  ≡
  false
canonicalProofAuthorityIsFalse =
  refl

------------------------------------------------------------------------
-- Collapsed-operation lemmas.

oddCoeffExtractorIsOddCoeff :
  (receipt : OddGrassmannLaneReceipt) →
  oddCoeffExtractor receipt ≡ oddCoeff receipt
oddCoeffExtractorIsOddCoeff receipt =
  refl

differentiationCollapsesToOddCoeffExtractor :
  (receipt : OddGrassmannLaneReceipt) →
  differentiation receipt ≡ oddCoeffExtractor receipt
differentiationCollapsesToOddCoeffExtractor receipt =
  refl

integrationCollapsesToOddCoeffExtractor :
  (receipt : OddGrassmannLaneReceipt) →
  integration receipt ≡ oddCoeffExtractor receipt
integrationCollapsesToOddCoeffExtractor receipt =
  refl

probeCollapsesToOddCoeffExtractor :
  (receipt : OddGrassmannLaneReceipt) →
  probe receipt ≡ oddCoeffExtractor receipt
probeCollapsesToOddCoeffExtractor receipt =
  refl

measureCollapsesToOddCoeffExtractor :
  (receipt : OddGrassmannLaneReceipt) →
  measure receipt ≡ oddCoeffExtractor receipt
measureCollapsesToOddCoeffExtractor receipt =
  refl

oddDerivativeCollapsesToOddCoeffExtractor :
  (receipt : OddGrassmannLaneReceipt) →
  oddDerivative receipt ≡ oddCoeffExtractor receipt
oddDerivativeCollapsesToOddCoeffExtractor receipt =
  refl

oddIntegralCollapsesToOddCoeffExtractor :
  (receipt : OddGrassmannLaneReceipt) →
  oddIntegral receipt ≡ oddCoeffExtractor receipt
oddIntegralCollapsesToOddCoeffExtractor receipt =
  refl

oddProbeCollapsesToOddCoeffExtractor :
  (receipt : OddGrassmannLaneReceipt) →
  oddProbe receipt ≡ oddCoeffExtractor receipt
oddProbeCollapsesToOddCoeffExtractor receipt =
  refl

oddMeasureCollapsesToOddCoeffExtractor :
  (receipt : OddGrassmannLaneReceipt) →
  oddMeasure receipt ≡ oddCoeffExtractor receipt
oddMeasureCollapsesToOddCoeffExtractor receipt =
  refl

canonicalNilpotentWitnessIsCanonical :
  nilpotentWitness canonicalOddGrassmannLaneReceipt
  ≡
  "theta^2 = 0"
canonicalNilpotentWitnessIsCanonical =
  refl

canonicalAuthorityGateIsFalse :
  authorityGate canonicalOddGrassmannLaneReceipt
  ≡
  false
canonicalAuthorityGateIsFalse =
  refl
