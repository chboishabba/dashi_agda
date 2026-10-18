module DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationExact as Ingest
import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact as Canonical

------------------------------------------------------------------------
-- INGEST-1 canonical weld.
--
-- This is the typed strengthening of the policy-level generic-ingest owner.
-- Provider structure remains family-specific, but every content-bearing source
-- is welded to the already-existing canonical EvidenceManifestation /
-- EvidenceSourceRevision / EvidenceSpan substrate.
------------------------------------------------------------------------

record GenericCompiledSource : Set where
  constructor generic-compiled-source
  field
    family : Ingest.SourceFamily
    role : Ingest.IngestRoleClass
    providerRef : String

    manifestation : Canonical.EvidenceManifestation
    revision : Canonical.EvidenceSourceRevision

    revisionSourceMatchesManifestation :
      Canonical.revisionSourceRevisionRef revision
      ≡ Canonical.manifestationSourceRevisionRef manifestation

    revisionManifestationMatches :
      Canonical.revisionManifestationRef revision
      ≡ Canonical.manifestationRef manifestation

    revisionDigestMatchesManifestation :
      Canonical.revisionContentDigestRef revision
      ≡ Canonical.manifestationContentDigestRef manifestation

    providerSpecificReviewShortcut : Bool
    providerSpecificReviewShortcutIsFalse :
      providerSpecificReviewShortcut ≡ false

    providerSpecificProjectionShortcut : Bool
    providerSpecificProjectionShortcutIsFalse :
      providerSpecificProjectionShortcut ≡ false

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open GenericCompiledSource public

data SemanticRegionEligibility : Set where
  semanticCandidate transportOnly structuralOnly observerOnly unknownEligibility :
    SemanticRegionEligibility

record GenericSourceRegion (source : GenericCompiledSource) : Set where
  constructor generic-source-region
  field
    regionRef : String
    anchor : Canonical.EvidenceSpan

    anchorUsesSourceRevision :
      Canonical.spanSourceRevisionRef anchor
      ≡ Canonical.revisionSourceRevisionRef
          (GenericCompiledSource.revision source)

    eligibility : SemanticRegionEligibility

    structureCreatesSemanticObservation : Bool
    structureCreatesSemanticObservationIsFalse :
      structureCreatesSemanticObservation ≡ false

    structureCreatesClaimTruth : Bool
    structureCreatesClaimTruthIsFalse :
      structureCreatesClaimTruth ≡ false

open GenericSourceRegion public

------------------------------------------------------------------------
-- Candidate observations use the exact region anchor and same revision.
------------------------------------------------------------------------

record CompiledRegionCandidate
    (source : GenericCompiledSource)
    (region : GenericSourceRegion source) : Set where
  constructor compiled-region-candidate
  field
    canonicalObservation : Canonical.EvidenceObservation

    observationUsesRegionAnchor :
      Canonical.observationSpan canonicalObservation
      ≡ GenericSourceRegion.anchor region

    observationRevisionWeld :
      Canonical.ObservationRevisionWeld canonicalObservation

    parserReceiptRef : String

    parserSuccessCreatesReviewPayment : Bool
    parserSuccessCreatesReviewPaymentIsFalse :
      parserSuccessCreatesReviewPayment ≡ false

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open CompiledRegionCandidate public

------------------------------------------------------------------------
-- Parser residuals are still source-backed regions.
------------------------------------------------------------------------

record RegionCompilationResidual
    (source : GenericCompiledSource)
    (region : GenericSourceRegion source) : Set where
  constructor region-compilation-residual
  field
    parserReceiptRef : String
    errorRef : String

    sourceRegionPreserved : Bool
    sourceRegionPreservedIsTrue :
      sourceRegionPreserved ≡ true

    createsAbsenceFinding : Bool
    createsAbsenceFindingIsFalse :
      createsAbsenceFinding ≡ false

    createsPropositionAbsence : Bool
    createsPropositionAbsenceIsFalse :
      createsPropositionAbsence ≡ false

    createsEventAbsence : Bool
    createsEventAbsenceIsFalse :
      createsEventAbsence ≡ false

    createsFalsehood : Bool
    createsFalsehoodIsFalse :
      createsFalsehood ≡ false

open RegionCompilationResidual public

------------------------------------------------------------------------
-- Lossless classification.
--
-- There is no unaccounted constructor.  Every admitted source region in a
-- lossless receipt is paired with exactly one of these four outcomes.
------------------------------------------------------------------------

data RegionCompilationOutcome
    (source : GenericCompiledSource)
    (region : GenericSourceRegion source) : Set where
  compiledCandidate :
    CompiledRegionCandidate source region →
    RegionCompilationOutcome source region

  parserResidual :
    RegionCompilationResidual source region →
    RegionCompilationOutcome source region

  transportRegion :
    GenericSourceRegion.eligibility region ≡ transportOnly →
    RegionCompilationOutcome source region

  structuralRegion :
    GenericSourceRegion.eligibility region ≡ structuralOnly →
    RegionCompilationOutcome source region

record RegionCompilationAssignment
    (source : GenericCompiledSource) : Set where
  constructor region-compilation-assignment
  field
    region : GenericSourceRegion source
    outcome : RegionCompilationOutcome source region

open RegionCompilationAssignment public

record LosslessCompilationReceipt
    (source : GenericCompiledSource) : Set where
  constructor lossless-compilation-receipt
  field
    assignments : List (RegionCompilationAssignment source)

    parseFailureDeletesSource : Bool
    parseFailureDeletesSourceIsFalse :
      parseFailureDeletesSource ≡ false

    candidateInterpretationDeterminesTruth : Bool
    candidateInterpretationDeterminesTruthIsFalse :
      candidateInterpretationDeterminesTruth ≡ false

    documentStructureCreatesObservationAutomatically : Bool
    documentStructureCreatesObservationAutomaticallyIsFalse :
      documentStructureCreatesObservationAutomatically ≡ false

    reviewAcceptanceCreatesClaimTruth : Bool
    reviewAcceptanceCreatesClaimTruthIsFalse :
      reviewAcceptanceCreatesClaimTruth ≡ false

    providerAdapterCreatesAlternateCanonicalCarrier : Bool
    providerAdapterCreatesAlternateCanonicalCarrierIsFalse :
      providerAdapterCreatesAlternateCanonicalCarrier ≡ false

open LosslessCompilationReceipt public

------------------------------------------------------------------------
-- Generic firewalls inherited from the specialist full-text pattern.
------------------------------------------------------------------------

data ProviderAdapterCreatesAlternateCanonicalCarrier : Set where
data StructuralRegionAutomaticallyBecomesSemanticCandidate : Set where
data UnknownRegionAutomaticallyBecomesSemanticCandidate : Set where
data ProviderAdapterCreatesReviewShortcut : Set where
data ProviderAdapterCreatesProjectionShortcut : Set where
data DocumentStructureCreatesSemanticObservation : Set where
data ParserSuccessCreatesReviewPayment : Set where
data ReviewAcceptanceCreatesClaimTruth : Set where
data ParserResidualCreatesSourceAbsence : Set where
data ParserResidualCreatesPropositionAbsence : Set where
data ParserResidualCreatesEventAbsence : Set where
data ParserResidualCreatesFalsehood : Set where

providerAdapterDoesNotCreateAlternateCanonicalCarrier :
  ProviderAdapterCreatesAlternateCanonicalCarrier → ⊥
providerAdapterDoesNotCreateAlternateCanonicalCarrier ()

structuralRegionDoesNotAutomaticallyBecomeSemanticCandidate :
  StructuralRegionAutomaticallyBecomesSemanticCandidate → ⊥
structuralRegionDoesNotAutomaticallyBecomeSemanticCandidate ()

unknownRegionDoesNotAutomaticallyBecomeSemanticCandidate :
  UnknownRegionAutomaticallyBecomesSemanticCandidate → ⊥
unknownRegionDoesNotAutomaticallyBecomeSemanticCandidate ()

providerAdapterDoesNotCreateReviewShortcut :
  ProviderAdapterCreatesReviewShortcut → ⊥
providerAdapterDoesNotCreateReviewShortcut ()

providerAdapterDoesNotCreateProjectionShortcut :
  ProviderAdapterCreatesProjectionShortcut → ⊥
providerAdapterDoesNotCreateProjectionShortcut ()

documentStructureDoesNotCreateSemanticObservation :
  DocumentStructureCreatesSemanticObservation → ⊥
documentStructureDoesNotCreateSemanticObservation ()

parserSuccessDoesNotCreateReviewPayment :
  ParserSuccessCreatesReviewPayment → ⊥
parserSuccessDoesNotCreateReviewPayment ()

reviewAcceptanceDoesNotCreateClaimTruth :
  ReviewAcceptanceCreatesClaimTruth → ⊥
reviewAcceptanceDoesNotCreateClaimTruth ()

parserResidualDoesNotCreateSourceAbsence :
  ParserResidualCreatesSourceAbsence → ⊥
parserResidualDoesNotCreateSourceAbsence ()

parserResidualDoesNotCreatePropositionAbsence :
  ParserResidualCreatesPropositionAbsence → ⊥
parserResidualDoesNotCreatePropositionAbsence ()

parserResidualDoesNotCreateEventAbsence :
  ParserResidualCreatesEventAbsence → ⊥
parserResidualDoesNotCreateEventAbsence ()

parserResidualDoesNotCreateFalsehood :
  ParserResidualCreatesFalsehood → ⊥
parserResidualDoesNotCreateFalsehood ()
