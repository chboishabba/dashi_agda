module DASHI.Core.SuperPayloadReadingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only boundary for reading super payloads.
--
-- This module treats `R^{p|q}` as an even carrier body plus odd nilpotent
-- witness lanes.  It does not reinterpret the notation as `p + q`
-- ordinary dimensions.  The record is intentionally import-friendly and
-- keeps promotion and semantic authority explicitly closed.

one :
  Nat
one =
  suc zero

zeroNat :
  Nat
zeroNat =
  zero

record SuperPayloadReadingBoundary : Set where
  constructor mkSuperPayloadReadingBoundary
  field
    payloadLabel :
      String

    notation :
      String

    bodyLabel :
      String

    sheafLabel :
      String

    readingLabel :
      String

    bodyReading :
      String

    sheafReading :
      String

    oddNilpotentWitnessReading :
      String

    oneOddCoordinateExample :
      String

    localStructureExample :
      String

    evenCarrierDimension :
      Nat

    oddWitnessDimension :
      Nat

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

open SuperPayloadReadingBoundary public

------------------------------------------------------------------------
-- Canonical boundary.

canonicalSuperPayloadReadingBoundary :
  SuperPayloadReadingBoundary
canonicalSuperPayloadReadingBoundary =
  mkSuperPayloadReadingBoundary
    "super payload reading boundary"
    "R^{p|q}"
    "even carrier body"
    "odd nilpotent witness sheaf"
    "R^{p|q} reads as even body plus odd witness lanes"
    "body: R^p"
    "sheaf: C∞_X tensor Λ(theta_1,...,theta_q)"
    "odd witness lanes live in the sheaf/algebra"
    "R^{0|1} = (*, Λ(theta))"
    "f(theta) = a + b theta"
    zeroNat
    one
    true
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Canonical projections.

canonicalPayloadLabelIsCanonical :
  payloadLabel canonicalSuperPayloadReadingBoundary
  ≡
  "super payload reading boundary"
canonicalPayloadLabelIsCanonical =
  refl

canonicalNotationIsCanonical :
  notation canonicalSuperPayloadReadingBoundary
  ≡
  "R^{p|q}"
canonicalNotationIsCanonical =
  refl

canonicalBodyLabelIsCanonical :
  bodyLabel canonicalSuperPayloadReadingBoundary
  ≡
  "even carrier body"
canonicalBodyLabelIsCanonical =
  refl

canonicalSheafLabelIsCanonical :
  sheafLabel canonicalSuperPayloadReadingBoundary
  ≡
  "odd nilpotent witness sheaf"
canonicalSheafLabelIsCanonical =
  refl

canonicalReadingLabelIsCanonical :
  readingLabel canonicalSuperPayloadReadingBoundary
  ≡
  "R^{p|q} reads as even body plus odd witness lanes"
canonicalReadingLabelIsCanonical =
  refl

canonicalBodyReadingIsCanonical :
  bodyReading canonicalSuperPayloadReadingBoundary
  ≡
  "body: R^p"
canonicalBodyReadingIsCanonical =
  refl

canonicalSheafReadingIsCanonical :
  sheafReading canonicalSuperPayloadReadingBoundary
  ≡
  "sheaf: C∞_X tensor Λ(theta_1,...,theta_q)"
canonicalSheafReadingIsCanonical =
  refl

canonicalOddNilpotentWitnessReadingIsCanonical :
  oddNilpotentWitnessReading canonicalSuperPayloadReadingBoundary
  ≡
  "odd witness lanes live in the sheaf/algebra"
canonicalOddNilpotentWitnessReadingIsCanonical =
  refl

canonicalOneOddCoordinateExampleIsTheta :
  oneOddCoordinateExample canonicalSuperPayloadReadingBoundary
  ≡
  "R^{0|1} = (*, Λ(theta))"
canonicalOneOddCoordinateExampleIsTheta =
  refl

canonicalLocalStructureExampleIsCanonical :
  localStructureExample canonicalSuperPayloadReadingBoundary
  ≡
  "f(theta) = a + b theta"
canonicalLocalStructureExampleIsCanonical =
  refl

canonicalEvenCarrierDimensionIsZero :
  evenCarrierDimension canonicalSuperPayloadReadingBoundary
  ≡
  zeroNat
canonicalEvenCarrierDimensionIsZero =
  refl

canonicalOddWitnessDimensionIsOne :
  oddWitnessDimension canonicalSuperPayloadReadingBoundary
  ≡
  one
canonicalOddWitnessDimensionIsOne =
  refl

canonicalCandidateOnlyIsTrue :
  candidateOnly canonicalSuperPayloadReadingBoundary
  ≡
  true
canonicalCandidateOnlyIsTrue =
  refl

canonicalPromotedIsFalse :
  promoted canonicalSuperPayloadReadingBoundary
  ≡
  false
canonicalPromotedIsFalse =
  refl

canonicalSemanticAuthorityIsFalse :
  semanticAuthority canonicalSuperPayloadReadingBoundary
  ≡
  false
canonicalSemanticAuthorityIsFalse =
  refl
