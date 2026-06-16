module DASHI.Crypto.RSAVulnerabilityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as ArithmeticIntegerEmbedding
import DASHI.Arithmetic.CoprimeLayer as CoprimeLayer
import DASHI.Arithmetic.VpDepth as VpDepth
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.HiddenLiftProjectionCore as HiddenLiftProjectionCore

------------------------------------------------------------------------
-- Candidate-only RSA vulnerability boundary.
--
-- This module records a fail-closed boundary for RSA-adjacent candidate
-- surfaces.  It names the local vocabulary for common vulnerability patterns
-- and keeps every authority-bearing claim blocked.
--
-- The imported arithmetic modules are referenced here only as lightweight
-- labels and future integration anchors.  If HiddenLiftProjectionCore later
-- exposes a concrete receipt surface in this fork, this module can be wired
-- to it without changing the boundary vocabulary below.

data RSAVulnerabilityKind : Set where
  visibleAxisSmallFactorKind :
    RSAVulnerabilityKind

  sharedPrimeModulusCollapseKind :
    RSAVulnerabilityKind

  fermatClosePrimeChamberKind :
    RSAVulnerabilityKind

  badExponentShortInverseWitnessKind :
    RSAVulnerabilityKind

  paddingEncodingCollisionKind :
    RSAVulnerabilityKind

  statisticalSideChannelWeaknessKind :
    RSAVulnerabilityKind

  namedRSAVulnerabilityKind :
    String →
    RSAVulnerabilityKind

canonicalRSAVulnerabilityKinds : List RSAVulnerabilityKind
canonicalRSAVulnerabilityKinds =
  visibleAxisSmallFactorKind
  ∷ sharedPrimeModulusCollapseKind
  ∷ fermatClosePrimeChamberKind
  ∷ badExponentShortInverseWitnessKind
  ∷ paddingEncodingCollisionKind
  ∷ statisticalSideChannelWeaknessKind
  ∷ []

data RSAAuthorityClaim : Set where
  generalRSABreakClaim :
    RSAAuthorityClaim

  factoringHardnessTheoremClaim :
    RSAAuthorityClaim

  semanticSecurityProofClaim :
    RSAAuthorityClaim

  paddingSecurityProofClaim :
    RSAAuthorityClaim

  implementationOrSideChannelAuthorityClaim :
    RSAAuthorityClaim

data RSABlockedWitnessKind : Set where
  visibleAxisSmallFactorWitness :
    RSABlockedWitnessKind

  sharedPrimeModulusCollapseWitness :
    RSABlockedWitnessKind

  fermatClosePrimeChamberWitness :
    RSABlockedWitnessKind

  badExponentShortInverseWitness :
    RSABlockedWitnessKind

  paddingEncodingCollisionWitness :
    RSABlockedWitnessKind

  statisticalSideChannelWeaknessWitness :
    RSABlockedWitnessKind

record RSABlockedAuthority : Set where
  constructor mkRSABlockedAuthority
  field
    blockedAuthorityLabel :
      String

    blockedAuthorityClaim :
      RSAAuthorityClaim

    blockedAuthorityNotes :
      String

    blockedAuthority :
      Bool

    blockedAuthorityIsFalse :
      blockedAuthority ≡ false

open RSABlockedAuthority public

record RSABlockedWitness : Set where
  constructor mkRSABlockedWitness
  field
    blockedWitnessKind :
      RSABlockedWitnessKind

    blockedWitnessLabel :
      String

    blockedWitnessSurface :
      String

    blockedWitnessClaim :
      String

    blockedWitness :
      Bool

    blockedWitnessIsFalse :
      blockedWitness ≡ false

open RSABlockedWitness public

record RSAVulnerabilityShape : Set where
  constructor mkRSAVulnerabilityShape
  field
    shapeKind :
      RSAVulnerabilityKind

    shapeLabel :
      String

    shapeSurface :
      String

    shapeGenericReceiptLabel :
      String

    shapeGenericReceiptSurface :
      String

    shapeCandidateOnly :
      Bool

    shapeCandidateOnlyIsTrue :
      shapeCandidateOnly ≡ true

    shapePromoted :
      Bool

    shapePromotedIsFalse :
      shapePromoted ≡ false

    shapeBlockedAuthority :
      RSABlockedAuthority

    shapeBlockedWitness :
      RSABlockedWitness

open RSAVulnerabilityShape public

------------------------------------------------------------------------
-- Canonical blocked-authority rows.

generalRSABreakBlockedAuthority :
  RSABlockedAuthority
generalRSABreakBlockedAuthority =
  mkRSABlockedAuthority
    "general RSA break"
    generalRSABreakClaim
    "No general RSA break is proved or promoted here."
    false
    refl

factoringHardnessTheoremBlockedAuthority :
  RSABlockedAuthority
factoringHardnessTheoremBlockedAuthority =
  mkRSABlockedAuthority
    "factoring-hardness theorem"
    factoringHardnessTheoremClaim
    "No factoring-hardness theorem is discharged in this boundary."
    false
    refl

semanticSecurityProofBlockedAuthority :
  RSABlockedAuthority
semanticSecurityProofBlockedAuthority =
  mkRSABlockedAuthority
    "semantic-security proof"
    semanticSecurityProofClaim
    "No semantic-security proof is supplied here."
    false
    refl

paddingSecurityProofBlockedAuthority :
  RSABlockedAuthority
paddingSecurityProofBlockedAuthority =
  mkRSABlockedAuthority
    "padding-security proof"
    paddingSecurityProofClaim
    "No padding-security proof is supplied here."
    false
    refl

implementationOrSideChannelAuthorityBlockedAuthority :
  RSABlockedAuthority
implementationOrSideChannelAuthorityBlockedAuthority =
  mkRSABlockedAuthority
    "implementation or side-channel authority"
    implementationOrSideChannelAuthorityClaim
    "No implementation-level or side-channel authority is asserted here."
    false
    refl

------------------------------------------------------------------------
-- Canonical blocked-witness rows.

visibleAxisSmallFactorBlockedWitness :
  RSABlockedWitness
visibleAxisSmallFactorBlockedWitness =
  mkRSABlockedWitness
    visibleAxisSmallFactorWitness
    "visible-axis small factor"
    "visible-axis small-factor lane"
    "labelled as a candidate-only small-factor witness, not as an extracted factor"
    false
    refl

sharedPrimeModulusCollapseBlockedWitness :
  RSABlockedWitness
sharedPrimeModulusCollapseBlockedWitness =
  mkRSABlockedWitness
    sharedPrimeModulusCollapseWitness
    "shared-prime modulus collapse"
    "shared-prime modulus-collapse lane"
    "labelled as a candidate-only modulus-collapse witness, not as a live CRT recovery"
    false
    refl

fermatClosePrimeChamberBlockedWitness :
  RSABlockedWitness
fermatClosePrimeChamberBlockedWitness =
  mkRSABlockedWitness
    fermatClosePrimeChamberWitness
    "Fermat close-prime chamber"
    "Fermat close-prime chamber lane"
    "labelled as a candidate-only close-prime chamber witness, not as a factorization result"
    false
    refl

badExponentShortInverseBlockedWitness :
  RSABlockedWitness
badExponentShortInverseBlockedWitness =
  mkRSABlockedWitness
    badExponentShortInverseWitness
    "bad exponent / short inverse"
    "bad-exponent short-inverse lane"
    "labelled as a candidate-only inverse witness, not as a decryption authority"
    false
    refl

paddingEncodingCollisionBlockedWitness :
  RSABlockedWitness
paddingEncodingCollisionBlockedWitness =
  mkRSABlockedWitness
    paddingEncodingCollisionWitness
    "padding / encoding collision"
    "padding-encoding collision lane"
    "labelled as a candidate-only collision witness, not as a padding-security theorem"
    false
    refl

statisticalSideChannelWeaknessBlockedWitness :
  RSABlockedWitness
statisticalSideChannelWeaknessBlockedWitness =
  mkRSABlockedWitness
    statisticalSideChannelWeaknessWitness
    "statistical side-channel weakness"
    "statistical side-channel weakness lane"
    "labelled as a candidate-only weakness witness, not as implementation or attack authority"
    false
    refl

------------------------------------------------------------------------
-- Canonical vulnerability shapes.

visibleAxisSmallFactorShape :
  RSAVulnerabilityShape
visibleAxisSmallFactorShape =
  mkRSAVulnerabilityShape
    visibleAxisSmallFactorKind
    "visible-axis small factor"
    "RSA visible-axis small-factor candidate boundary"
    "DASHI.Core.GenericReceipt"
    "DASHI.Core.HiddenLiftProjectionCore"
    true
    refl
    false
    refl
    generalRSABreakBlockedAuthority
    visibleAxisSmallFactorBlockedWitness

sharedPrimeModulusCollapseShape :
  RSAVulnerabilityShape
sharedPrimeModulusCollapseShape =
  mkRSAVulnerabilityShape
    sharedPrimeModulusCollapseKind
    "shared-prime modulus collapse"
    "RSA shared-prime modulus-collapse candidate boundary"
    "DASHI.Core.GenericReceipt"
    "DASHI.Core.HiddenLiftProjectionCore"
    true
    refl
    false
    refl
    generalRSABreakBlockedAuthority
    sharedPrimeModulusCollapseBlockedWitness

fermatClosePrimeChamberShape :
  RSAVulnerabilityShape
fermatClosePrimeChamberShape =
  mkRSAVulnerabilityShape
    fermatClosePrimeChamberKind
    "Fermat close-prime chamber"
    "RSA Fermat close-prime chamber candidate boundary"
    "DASHI.Core.GenericReceipt"
    "DASHI.Core.HiddenLiftProjectionCore"
    true
    refl
    false
    refl
    factoringHardnessTheoremBlockedAuthority
    fermatClosePrimeChamberBlockedWitness

badExponentShortInverseWitnessShape :
  RSAVulnerabilityShape
badExponentShortInverseWitnessShape =
  mkRSAVulnerabilityShape
    badExponentShortInverseWitnessKind
    "bad exponent / short inverse witness"
    "RSA bad-exponent short-inverse candidate boundary"
    "DASHI.Core.GenericReceipt"
    "DASHI.Core.HiddenLiftProjectionCore"
    true
    refl
    false
    refl
    semanticSecurityProofBlockedAuthority
    badExponentShortInverseBlockedWitness

paddingEncodingCollisionShape :
  RSAVulnerabilityShape
paddingEncodingCollisionShape =
  mkRSAVulnerabilityShape
    paddingEncodingCollisionKind
    "padding / encoding collision"
    "RSA padding-encoding collision candidate boundary"
    "DASHI.Core.GenericReceipt"
    "DASHI.Core.HiddenLiftProjectionCore"
    true
    refl
    false
    refl
    paddingSecurityProofBlockedAuthority
    paddingEncodingCollisionBlockedWitness

statisticalSideChannelWeaknessShape :
  RSAVulnerabilityShape
statisticalSideChannelWeaknessShape =
  mkRSAVulnerabilityShape
    statisticalSideChannelWeaknessKind
    "statistical side-channel weakness"
    "RSA statistical side-channel weakness candidate boundary"
    "DASHI.Core.GenericReceipt"
    "DASHI.Core.HiddenLiftProjectionCore"
    true
    refl
    false
    refl
    implementationOrSideChannelAuthorityBlockedAuthority
    statisticalSideChannelWeaknessBlockedWitness

canonicalRSAVulnerabilityShapes :
  List RSAVulnerabilityShape
canonicalRSAVulnerabilityShapes =
  visibleAxisSmallFactorShape
  ∷ sharedPrimeModulusCollapseShape
  ∷ fermatClosePrimeChamberShape
  ∷ badExponentShortInverseWitnessShape
  ∷ paddingEncodingCollisionShape
  ∷ statisticalSideChannelWeaknessShape
  ∷ []

------------------------------------------------------------------------
-- Boundary receipt surface.

record RSAVulnerabilityBoundary : Set where
  constructor mkRSAVulnerabilityBoundary
  field
    boundaryLabel :
      String

    boundarySurface :
      String

    arithmeticCoprimeLayerReference :
      String

    arithmeticVpDepthReference :
      String

    arithmeticIntegerEmbeddingReference :
      String

    hiddenLiftProjectionReference :
      String

    boundaryReceipt :
      GenericReceipt.GenericReceipt

    boundaryCandidateOnly :
      Bool

    boundaryCandidateOnlyIsTrue :
      boundaryCandidateOnly ≡ true

    boundaryPromoted :
      Bool

    boundaryPromotedIsFalse :
      boundaryPromoted ≡ false

    generalRSABreakBlocked :
      Bool

    generalRSABreakBlockedIsFalse :
      generalRSABreakBlocked ≡ false

    factoringHardnessTheoremBlocked :
      Bool

    factoringHardnessTheoremBlockedIsFalse :
      factoringHardnessTheoremBlocked ≡ false

    semanticSecurityProofBlocked :
      Bool

    semanticSecurityProofBlockedIsFalse :
      semanticSecurityProofBlocked ≡ false

    paddingSecurityProofBlocked :
      Bool

    paddingSecurityProofBlockedIsFalse :
      paddingSecurityProofBlocked ≡ false

    implementationOrSideChannelAuthorityBlocked :
      Bool

    implementationOrSideChannelAuthorityBlockedIsFalse :
      implementationOrSideChannelAuthorityBlocked ≡ false

    vulnerabilityShapes :
      List RSAVulnerabilityShape

    vulnerabilityShapesAreCanonical :
      vulnerabilityShapes ≡ canonicalRSAVulnerabilityShapes

open RSAVulnerabilityBoundary public

canonicalRSAVulnerabilityBoundaryReceipt :
  GenericReceipt.GenericReceipt
canonicalRSAVulnerabilityBoundaryReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "RSA vulnerability boundary"
    "DASHI.Crypto.RSAVulnerabilityBoundary"
    "canonicalRSAVulnerabilityBoundary"
    "candidate-only RSA vulnerability boundary with blocked authority lanes for small-factor, shared-prime, close-prime, bad-exponent, padding-collision, and side-channel surfaces"
    "general RSA break, factoring-hardness theorem, semantic-security proof, padding-security proof, and implementation/side-channel authority remain blocked"
    "agda -i . DASHI/Crypto/RSAVulnerabilityBoundary.agda"

canonicalRSAVulnerabilityBoundary :
  RSAVulnerabilityBoundary
canonicalRSAVulnerabilityBoundary =
  mkRSAVulnerabilityBoundary
    "RSA vulnerability boundary"
    "candidate-only RSA vulnerability boundary"
    "DASHI.Arithmetic.CoprimeLayer"
    "DASHI.Arithmetic.VpDepth"
    "DASHI.Arithmetic.ArithmeticIntegerEmbedding"
    "DASHI.Core.HiddenLiftProjectionCore"
    canonicalRSAVulnerabilityBoundaryReceipt
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
    false
    refl
    canonicalRSAVulnerabilityShapes
    refl

------------------------------------------------------------------------
-- Compact, string-only integration labels.

canonicalRSAVulnerabilityBoundaryLabels :
  List String
canonicalRSAVulnerabilityBoundaryLabels =
  "DASHI.Arithmetic.CoprimeLayer"
  ∷ "DASHI.Arithmetic.VpDepth"
  ∷ "DASHI.Arithmetic.ArithmeticIntegerEmbedding"
  ∷ "DASHI.Core.GenericReceipt"
  ∷ "DASHI.Core.HiddenLiftProjectionCore"
  ∷ "visible-axis small factor"
  ∷ "shared-prime modulus collapse"
  ∷ "Fermat close-prime chamber"
  ∷ "bad exponent / short inverse witness"
  ∷ "padding / encoding collision"
  ∷ "statistical side-channel weakness"
  ∷ []
