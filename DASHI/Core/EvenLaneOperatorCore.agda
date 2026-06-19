module DASHI.Core.EvenLaneOperatorCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Even lane operator surface.
--
-- The even lane keeps derivative, probe, and local variation separate
-- from integral, measure, and global accumulation.  The receipt stays
-- candidate-only, and the canonical shape is recorded directly in
-- the projections below.

record EvenLaneOperatorReceipt : Set where
  constructor mkEvenLaneOperatorReceipt
  field
    payloadLabel :
      String

    payloadOwner :
      String

    payloadSurface :
      String

    derivativeSurface :
      String

    probeSurface :
      String

    localVariationSurface :
      String

    integralSurface :
      String

    measureSurface :
      String

    globalAccumulationSurface :
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

open EvenLaneOperatorReceipt public

------------------------------------------------------------------------
-- Canonical receipt.

canonicalEvenLaneOperatorReceipt :
  EvenLaneOperatorReceipt
canonicalEvenLaneOperatorReceipt =
  mkEvenLaneOperatorReceipt
    "even lane operator core"
    "authority-canonical"
    "even lane surface"
    "derivative"
    "probe"
    "local variation"
    "integral"
    "measure"
    "global accumulation"
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
-- Operation accessors.

derivativeSurfaceExtractor :
  EvenLaneOperatorReceipt →
  String
derivativeSurfaceExtractor receipt =
  derivativeSurface receipt

probeSurfaceExtractor :
  EvenLaneOperatorReceipt →
  String
probeSurfaceExtractor receipt =
  probeSurface receipt

localVariationSurfaceExtractor :
  EvenLaneOperatorReceipt →
  String
localVariationSurfaceExtractor receipt =
  localVariationSurface receipt

integralSurfaceExtractor :
  EvenLaneOperatorReceipt →
  String
integralSurfaceExtractor receipt =
  integralSurface receipt

measureSurfaceExtractor :
  EvenLaneOperatorReceipt →
  String
measureSurfaceExtractor receipt =
  measureSurface receipt

globalAccumulationSurfaceExtractor :
  EvenLaneOperatorReceipt →
  String
globalAccumulationSurfaceExtractor receipt =
  globalAccumulationSurface receipt

derivative :
  EvenLaneOperatorReceipt →
  String
derivative =
  derivativeSurfaceExtractor

probe :
  EvenLaneOperatorReceipt →
  String
probe =
  probeSurfaceExtractor

localVariation :
  EvenLaneOperatorReceipt →
  String
localVariation =
  localVariationSurfaceExtractor

integral :
  EvenLaneOperatorReceipt →
  String
integral =
  integralSurfaceExtractor

measure :
  EvenLaneOperatorReceipt →
  String
measure =
  measureSurfaceExtractor

globalAccumulation :
  EvenLaneOperatorReceipt →
  String
globalAccumulation =
  globalAccumulationSurfaceExtractor

------------------------------------------------------------------------
-- Compatibility aliases.

differentiation :
  EvenLaneOperatorReceipt →
  String
differentiation =
  derivative

integration :
  EvenLaneOperatorReceipt →
  String
integration =
  integral

accumulation :
  EvenLaneOperatorReceipt →
  String
accumulation =
  globalAccumulation

evenDerivative :
  EvenLaneOperatorReceipt →
  String
evenDerivative =
  derivative

evenProbe :
  EvenLaneOperatorReceipt →
  String
evenProbe =
  probe

evenIntegral :
  EvenLaneOperatorReceipt →
  String
evenIntegral =
  integral

evenMeasure :
  EvenLaneOperatorReceipt →
  String
evenMeasure =
  measure

------------------------------------------------------------------------
-- Projection lemmas for the canonical receipt.

canonicalPayloadLabelIsCanonical :
  payloadLabel canonicalEvenLaneOperatorReceipt
  ≡
  "even lane operator core"
canonicalPayloadLabelIsCanonical =
  refl

canonicalPayloadOwnerIsCanonical :
  payloadOwner canonicalEvenLaneOperatorReceipt
  ≡
  "authority-canonical"
canonicalPayloadOwnerIsCanonical =
  refl

canonicalPayloadSurfaceIsCanonical :
  payloadSurface canonicalEvenLaneOperatorReceipt
  ≡
  "even lane surface"
canonicalPayloadSurfaceIsCanonical =
  refl

canonicalDerivativeSurfaceIsCanonical :
  derivativeSurface canonicalEvenLaneOperatorReceipt
  ≡
  "derivative"
canonicalDerivativeSurfaceIsCanonical =
  refl

canonicalProbeSurfaceIsCanonical :
  probeSurface canonicalEvenLaneOperatorReceipt
  ≡
  "probe"
canonicalProbeSurfaceIsCanonical =
  refl

canonicalLocalVariationSurfaceIsCanonical :
  localVariationSurface canonicalEvenLaneOperatorReceipt
  ≡
  "local variation"
canonicalLocalVariationSurfaceIsCanonical =
  refl

canonicalIntegralSurfaceIsCanonical :
  integralSurface canonicalEvenLaneOperatorReceipt
  ≡
  "integral"
canonicalIntegralSurfaceIsCanonical =
  refl

canonicalMeasureSurfaceIsCanonical :
  measureSurface canonicalEvenLaneOperatorReceipt
  ≡
  "measure"
canonicalMeasureSurfaceIsCanonical =
  refl

canonicalGlobalAccumulationSurfaceIsCanonical :
  globalAccumulationSurface canonicalEvenLaneOperatorReceipt
  ≡
  "global accumulation"
canonicalGlobalAccumulationSurfaceIsCanonical =
  refl

canonicalCandidateOnlyIsTrue :
  candidateOnly canonicalEvenLaneOperatorReceipt
  ≡
  true
canonicalCandidateOnlyIsTrue =
  refl

canonicalPromotedIsFalse :
  promoted canonicalEvenLaneOperatorReceipt
  ≡
  false
canonicalPromotedIsFalse =
  refl

canonicalSemanticAuthorityIsFalse :
  semanticAuthority canonicalEvenLaneOperatorReceipt
  ≡
  false
canonicalSemanticAuthorityIsFalse =
  refl

canonicalMeasureAuthorityIsFalse :
  measureAuthority canonicalEvenLaneOperatorReceipt
  ≡
  false
canonicalMeasureAuthorityIsFalse =
  refl

canonicalVariationAuthorityIsFalse :
  variationAuthority canonicalEvenLaneOperatorReceipt
  ≡
  false
canonicalVariationAuthorityIsFalse =
  refl

canonicalProofAuthorityIsFalse :
  proofAuthority canonicalEvenLaneOperatorReceipt
  ≡
  false
canonicalProofAuthorityIsFalse =
  refl

------------------------------------------------------------------------
-- Accessor lemmas.

derivativeSurfaceExtractorIsDerivativeSurface :
  (receipt : EvenLaneOperatorReceipt) →
  derivativeSurfaceExtractor receipt ≡ derivativeSurface receipt
derivativeSurfaceExtractorIsDerivativeSurface receipt =
  refl

probeSurfaceExtractorIsProbeSurface :
  (receipt : EvenLaneOperatorReceipt) →
  probeSurfaceExtractor receipt ≡ probeSurface receipt
probeSurfaceExtractorIsProbeSurface receipt =
  refl

localVariationSurfaceExtractorIsLocalVariationSurface :
  (receipt : EvenLaneOperatorReceipt) →
  localVariationSurfaceExtractor receipt ≡ localVariationSurface receipt
localVariationSurfaceExtractorIsLocalVariationSurface receipt =
  refl

integralSurfaceExtractorIsIntegralSurface :
  (receipt : EvenLaneOperatorReceipt) →
  integralSurfaceExtractor receipt ≡ integralSurface receipt
integralSurfaceExtractorIsIntegralSurface receipt =
  refl

measureSurfaceExtractorIsMeasureSurface :
  (receipt : EvenLaneOperatorReceipt) →
  measureSurfaceExtractor receipt ≡ measureSurface receipt
measureSurfaceExtractorIsMeasureSurface receipt =
  refl

globalAccumulationSurfaceExtractorIsGlobalAccumulationSurface :
  (receipt : EvenLaneOperatorReceipt) →
  globalAccumulationSurfaceExtractor receipt ≡
  globalAccumulationSurface receipt
globalAccumulationSurfaceExtractorIsGlobalAccumulationSurface receipt =
  refl

differentiationCollapsesToDerivativeSurfaceExtractor :
  (receipt : EvenLaneOperatorReceipt) →
  differentiation receipt ≡ derivativeSurfaceExtractor receipt
differentiationCollapsesToDerivativeSurfaceExtractor receipt =
  refl

integrationCollapsesToIntegralSurfaceExtractor :
  (receipt : EvenLaneOperatorReceipt) →
  integration receipt ≡ integralSurfaceExtractor receipt
integrationCollapsesToIntegralSurfaceExtractor receipt =
  refl

probeCollapsesToProbeSurfaceExtractor :
  (receipt : EvenLaneOperatorReceipt) →
  probe receipt ≡ probeSurfaceExtractor receipt
probeCollapsesToProbeSurfaceExtractor receipt =
  refl

measureCollapsesToMeasureSurfaceExtractor :
  (receipt : EvenLaneOperatorReceipt) →
  measure receipt ≡ measureSurfaceExtractor receipt
measureCollapsesToMeasureSurfaceExtractor receipt =
  refl

localVariationCollapsesToLocalVariationSurfaceExtractor :
  (receipt : EvenLaneOperatorReceipt) →
  localVariation receipt ≡ localVariationSurfaceExtractor receipt
localVariationCollapsesToLocalVariationSurfaceExtractor receipt =
  refl

globalAccumulationCollapsesToGlobalAccumulationSurfaceExtractor :
  (receipt : EvenLaneOperatorReceipt) →
  globalAccumulation receipt ≡ globalAccumulationSurfaceExtractor receipt
globalAccumulationCollapsesToGlobalAccumulationSurfaceExtractor receipt =
  refl
