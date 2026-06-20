module DASHI.Core.OddBerezinTopCoefficientBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Multi-odd-variable Berezin boundary surface.
--
-- For q > 1, the candidate reading is that Berezin integration extracts
-- the ordered top coefficient [theta_q ... theta_1] F, but the sign is
-- convention-dependent.  This module records that order/sign convention
-- explicitly, keeps the extractor label visible, and fails closed on all
-- authority bits.

record OddBerezinTopCoefficientBoundaryReceipt : Set where
  constructor mkOddBerezinTopCoefficientBoundaryReceipt
  field
    payloadLabel :
      String

    payloadOwner :
      String

    payloadSurface :
      String

    oddVariableCount :
      String

    orderConventionCarrier :
      String

    signConventionCarrier :
      String

    topCoefficientExtractorLabel :
      String

    topCoefficientSurface :
      String

    berezinIntegrationReceipt :
      String

    qGreaterThanOne :
      Bool

    qGreaterThanOneIsTrue :
      qGreaterThanOne ≡ true

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    orderAuthority :
      Bool

    orderAuthorityIsFalse :
      orderAuthority ≡ false

    signAuthority :
      Bool

    signAuthorityIsFalse :
      signAuthority ≡ false

    extractorAuthority :
      Bool

    extractorAuthorityIsFalse :
      extractorAuthority ≡ false

    proofAuthority :
      Bool

    proofAuthorityIsFalse :
      proofAuthority ≡ false

open OddBerezinTopCoefficientBoundaryReceipt public

------------------------------------------------------------------------
-- Canonical candidate-only receipt.

canonicalOddBerezinTopCoefficientBoundaryReceipt :
  OddBerezinTopCoefficientBoundaryReceipt
canonicalOddBerezinTopCoefficientBoundaryReceipt =
  mkOddBerezinTopCoefficientBoundaryReceipt
    "odd berezin top coefficient boundary"
    "candidate-only"
    "q>1 ordered top coefficient [theta_q ... theta_1] F up to sign convention"
    "q > 1"
    "ordered theta_q ... theta_1"
    "convention-dependent sign"
    "[theta_q ... theta_1] coefficient"
    "[theta_q ... theta_1] F"
    "Berezin integration extracts the ordered top coefficient up to convention-dependent sign"
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
-- Surface accessors.

oddVariableCountCarrier :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
oddVariableCountCarrier =
  oddVariableCount

orderConventionCarrierOf :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
orderConventionCarrierOf =
  orderConventionCarrier

signConventionCarrierOf :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
signConventionCarrierOf =
  signConventionCarrier

topCoefficientExtractorLabelOf :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
topCoefficientExtractorLabelOf =
  topCoefficientExtractorLabel

topCoefficientSurfaceExtractor :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
topCoefficientSurfaceExtractor =
  topCoefficientSurface

berezinIntegration :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
berezinIntegration =
  topCoefficientSurfaceExtractor

integration :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
integration =
  berezinIntegration

extractTopCoefficient :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
extractTopCoefficient =
  topCoefficientSurfaceExtractor

orderedTopCoefficient :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
orderedTopCoefficient =
  topCoefficientSurfaceExtractor

topCoefficientExtractor :
  OddBerezinTopCoefficientBoundaryReceipt →
  String
topCoefficientExtractor =
  topCoefficientExtractorLabelOf

authorityGate :
  OddBerezinTopCoefficientBoundaryReceipt →
  Bool
authorityGate =
  promoted

------------------------------------------------------------------------
-- Projection lemmas for the canonical receipt.

canonicalPayloadLabelIsCanonical :
  payloadLabel canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "odd berezin top coefficient boundary"
canonicalPayloadLabelIsCanonical =
  refl

canonicalPayloadOwnerIsCanonical :
  payloadOwner canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "candidate-only"
canonicalPayloadOwnerIsCanonical =
  refl

canonicalPayloadSurfaceIsCanonical :
  payloadSurface canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "q>1 ordered top coefficient [theta_q ... theta_1] F up to sign convention"
canonicalPayloadSurfaceIsCanonical =
  refl

canonicalOddVariableCountIsCanonical :
  oddVariableCount canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "q > 1"
canonicalOddVariableCountIsCanonical =
  refl

canonicalOrderConventionIsCanonical :
  orderConventionCarrier canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "ordered theta_q ... theta_1"
canonicalOrderConventionIsCanonical =
  refl

canonicalSignConventionIsCanonical :
  signConventionCarrier canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "convention-dependent sign"
canonicalSignConventionIsCanonical =
  refl

canonicalTopCoefficientExtractorLabelIsCanonical :
  topCoefficientExtractorLabel canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "[theta_q ... theta_1] coefficient"
canonicalTopCoefficientExtractorLabelIsCanonical =
  refl

canonicalTopCoefficientSurfaceIsCanonical :
  topCoefficientSurface canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "[theta_q ... theta_1] F"
canonicalTopCoefficientSurfaceIsCanonical =
  refl

canonicalBerezinIntegrationReceiptIsCanonical :
  berezinIntegrationReceipt canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  "Berezin integration extracts the ordered top coefficient up to convention-dependent sign"
canonicalBerezinIntegrationReceiptIsCanonical =
  refl

canonicalQGreaterThanOneIsTrue :
  qGreaterThanOne canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  true
canonicalQGreaterThanOneIsTrue =
  refl

canonicalCandidateOnlyIsTrue :
  candidateOnly canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  true
canonicalCandidateOnlyIsTrue =
  refl

canonicalPromotedIsFalse :
  promoted canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  false
canonicalPromotedIsFalse =
  refl

canonicalOrderAuthorityIsFalse :
  orderAuthority canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  false
canonicalOrderAuthorityIsFalse =
  refl

canonicalSignAuthorityIsFalse :
  signAuthority canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  false
canonicalSignAuthorityIsFalse =
  refl

canonicalExtractorAuthorityIsFalse :
  extractorAuthority canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  false
canonicalExtractorAuthorityIsFalse =
  refl

canonicalProofAuthorityIsFalse :
  proofAuthority canonicalOddBerezinTopCoefficientBoundaryReceipt
  ≡
  false
canonicalProofAuthorityIsFalse =
  refl
