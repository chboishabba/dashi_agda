module DASHI.Interop.SLRCanonicalEvidenceSubstrateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- GOLDEN MIRROR OF SLR SPRINT-2 CANONICAL EVIDENCE SUBSTRATE
--
-- Runtime authority reviewed:
--   chboishabba/slr
--   branch: agent/sprint2-canonical-evidence-convergence
--   crates/sl-core/src/canonical_evidence.rs
--
-- This module mirrors the implemented M2.1/M2.2 evidence ABI:
--
--   EvidenceManifestation
--      -> EvidenceSourceRevision
--      -> EvidenceSpan
--      -> EvidenceObservation
--
-- M2.3 SharedEvidenceReducer is intentionally NOT modelled as implemented
-- production authority here. The SLR sprint board records it as the next
-- structural min-cut.
------------------------------------------------------------------------

data EvidenceManifestationFamily : Set where
  zelphHyperfabric wikidata wikipedia oalc legalAuthority pdfDocument
    transcript userEvidence otherEvidence : EvidenceManifestationFamily

record EvidenceManifestation : Set where
  constructor evidence-manifestation
  field
    manifestationRef : String
    manifestationFamily : EvidenceManifestationFamily
    manifestationSourceRef : String
    manifestationSourceRevisionRef : String
    manifestationContentDigestRef : String
    manifestationAcquisitionReceiptRef : String

    manifestationCandidateOnly : Bool
    manifestationCandidateOnlyIsTrue : manifestationCandidateOnly ≡ true

    manifestationCreatesSemanticAuthority : Bool
    manifestationCreatesSemanticAuthorityIsFalse : manifestationCreatesSemanticAuthority ≡ false

    manifestationApplicabilityPromoted : Bool
    manifestationApplicabilityPromotedIsFalse : manifestationApplicabilityPromoted ≡ false

    manifestationClaimTruthPromoted : Bool
    manifestationClaimTruthPromotedIsFalse : manifestationClaimTruthPromoted ≡ false

open EvidenceManifestation public

record EvidenceSourceRevision : Set where
  constructor evidence-source-revision
  field
    revisionSourceRevisionRef : String
    revisionManifestationRef : String
    revisionContentDigestRef : String
    revisionReceiptRef : String

open EvidenceSourceRevision public

data EvidenceSpanKind : Set where
  textRange : Nat → Nat → EvidenceSpanKind
  structuredCoordinate : String → EvidenceSpanKind
  wholeRevision : EvidenceSpanKind

record EvidenceSpan : Set where
  constructor evidence-span
  field
    spanSourceRevisionRef : String
    spanRef : String
    spanKind : EvidenceSpanKind

open EvidenceSpan public

record EvidenceObservation : Set where
  constructor evidence-observation
  field
    observationRef : String
    observationSourceRevisionRef : String
    observationSpan : EvidenceSpan
    predicateRef : String
    valueRef : String

    observationCandidateOnly : Bool
    observationCandidateOnlyIsTrue : observationCandidateOnly ≡ true

    observationCreatesSemanticAuthority : Bool
    observationCreatesSemanticAuthorityIsFalse : observationCreatesSemanticAuthority ≡ false

    observationApplicabilityPromoted : Bool
    observationApplicabilityPromotedIsFalse : observationApplicabilityPromoted ≡ false

    observationClaimTruthPromoted : Bool
    observationClaimTruthPromotedIsFalse : observationClaimTruthPromoted ≡ false

open EvidenceObservation public

------------------------------------------------------------------------
-- Same-revision weld remains explicit.
------------------------------------------------------------------------

record ObservationRevisionWeld (observation : EvidenceObservation) : Set where
  constructor observation-revision-weld
  field
    observationRevisionMatchesSpan :
      EvidenceObservation.observationSourceRevisionRef observation
      ≡ EvidenceSpan.spanSourceRevisionRef (EvidenceObservation.observationSpan observation)

open ObservationRevisionWeld public

------------------------------------------------------------------------
-- Application-level constructor surfaces. String non-emptiness remains a
-- runtime validation obligation in Rust; Agda records the semantic ABI and
-- non-promotion invariants.
------------------------------------------------------------------------

mkCandidateManifestation :
  String →
  EvidenceManifestationFamily →
  String →
  String →
  String →
  String →
  EvidenceManifestation
mkCandidateManifestation manifestation sourceFamily source revision digest acquisition =
  evidence-manifestation
    manifestation
    sourceFamily
    source
    revision
    digest
    acquisition
    true refl
    false refl
    false refl
    false refl

mkSourceRevision :
  EvidenceManifestation →
  String →
  EvidenceSourceRevision
mkSourceRevision m revisionReceipt =
  evidence-source-revision
    (EvidenceManifestation.manifestationSourceRevisionRef m)
    (EvidenceManifestation.manifestationRef m)
    (EvidenceManifestation.manifestationContentDigestRef m)
    revisionReceipt

mkTextRange :
  String → String → Nat → Nat → EvidenceSpan
mkTextRange revision spanId start end =
  evidence-span revision spanId (textRange start end)

mkStructuredCoordinate :
  String → String → String → EvidenceSpan
mkStructuredCoordinate revision spanId coordinate =
  evidence-span revision spanId (structuredCoordinate coordinate)

mkWholeRevision :
  String → String → EvidenceSpan
mkWholeRevision revision spanId =
  evidence-span revision spanId wholeRevision

mkCandidateObservation :
  String →
  String →
  EvidenceSpan →
  String →
  String →
  EvidenceObservation
mkCandidateObservation observation revision evidenceSpan predicate value =
  evidence-observation
    observation
    revision
    evidenceSpan
    predicate
    value
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls matching the Rust substrate.
------------------------------------------------------------------------

data ManifestationCreatesSemanticAuthority : Set where
data ManifestationCreatesClaimTruth : Set where
data ObservationCreatesSemanticAuthority : Set where
data ObservationCreatesClaimTruth : Set where
data ObservationPromotesApplicability : Set where
data StructuredCoordinateMustBecomeTextRange : Set where
data WholeRevisionMustBecomeTextRange : Set where
data SpanKindCreatesSemanticPreference : Set where
data CanonicalEvidenceCreatesDigitalESDAdmission : Set where
data SharedReducerAlreadyProductionCertified : Set where

manifestationDoesNotCreateSemanticAuthority :
  ManifestationCreatesSemanticAuthority → ⊥
manifestationDoesNotCreateSemanticAuthority ()

manifestationDoesNotCreateClaimTruth :
  ManifestationCreatesClaimTruth → ⊥
manifestationDoesNotCreateClaimTruth ()

observationDoesNotCreateSemanticAuthority :
  ObservationCreatesSemanticAuthority → ⊥
observationDoesNotCreateSemanticAuthority ()

observationDoesNotCreateClaimTruth :
  ObservationCreatesClaimTruth → ⊥
observationDoesNotCreateClaimTruth ()

observationDoesNotPromoteApplicability :
  ObservationPromotesApplicability → ⊥
observationDoesNotPromoteApplicability ()

structuredCoordinateDoesNotBecomeTextRange :
  StructuredCoordinateMustBecomeTextRange → ⊥
structuredCoordinateDoesNotBecomeTextRange ()

wholeRevisionDoesNotBecomeTextRange :
  WholeRevisionMustBecomeTextRange → ⊥
wholeRevisionDoesNotBecomeTextRange ()

spanKindDoesNotCreateSemanticPreference :
  SpanKindCreatesSemanticPreference → ⊥
spanKindDoesNotCreateSemanticPreference ()

canonicalEvidenceDoesNotCreateDigitalESDAdmission :
  CanonicalEvidenceCreatesDigitalESDAdmission → ⊥
canonicalEvidenceDoesNotCreateDigitalESDAdmission ()

sharedReducerNotYetProductionCertified :
  SharedReducerAlreadyProductionCertified → ⊥
sharedReducerNotYetProductionCertified ()

record SLRCanonicalEvidenceBoundary : Set where
  constructor slr-canonical-evidence-boundary
  field
    oneManifestationEnvelope : Bool
    oneManifestationEnvelopeIsTrue : oneManifestationEnvelope ≡ true

    oneRevisionSpanObservationSubstrate : Bool
    oneRevisionSpanObservationSubstrateIsTrue :
      oneRevisionSpanObservationSubstrate ≡ true

    textRangeSupported : Bool
    textRangeSupportedIsTrue : textRangeSupported ≡ true

    structuredCoordinateSupported : Bool
    structuredCoordinateSupportedIsTrue :
      structuredCoordinateSupported ≡ true

    wholeRevisionSupported : Bool
    wholeRevisionSupportedIsTrue : wholeRevisionSupported ≡ true

    candidateOnlyByDefault : Bool
    candidateOnlyByDefaultIsTrue : candidateOnlyByDefault ≡ true

    sharedReducerProductionCertified : Bool
    sharedReducerProductionCertifiedIsFalse :
      sharedReducerProductionCertified ≡ false

open SLRCanonicalEvidenceBoundary public

canonicalSLRCanonicalEvidenceBoundary : SLRCanonicalEvidenceBoundary
canonicalSLRCanonicalEvidenceBoundary =
  slr-canonical-evidence-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

slrSprint2EvidenceReading : String
slrSprint2EvidenceReading =
  "Golden mirror of the source-written SLR Sprint-2 M2.1/M2.2 canonical evidence substrate: one candidate-only EvidenceManifestation envelope lowers to EvidenceSourceRevision, then exact EvidenceSpan (TextRange, StructuredCoordinate or WholeRevision), then candidate-only EvidenceObservation. This carrier creates neither semantic authority, legal applicability nor claim truth. M2.3 SharedEvidenceReducer remains the next SLR structural min-cut and is not represented here as production-certified."
