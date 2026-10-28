module DASHI.Law.SensibLawNormativeDocsetIngestionExtractionContractExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)
open import Data.Nat using (_≤_)

import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationExact as Ingest
import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldExact as Weld
import DASHI.Education.DigitalESDDocumentTextMaterialisationExact as Text
import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact as Canonical
import DASHI.Law.SensibLawCanonicalJudgmentCitationCandidateExtractionExact as Judgment

------------------------------------------------------------------------
-- BOUNDED NORMATIVE-DOCSET INGESTION / EXTRACTION CONTRACT
--
-- This owner composes existing ingestion and extraction owners.
-- It does not define a second parser.
-- It does not define a second source identity.
-- It does not create semantic or legal authority.
------------------------------------------------------------------------

data NormativeSourceClass : Set where
  normativeDocument : NormativeSourceClass
  normativeLegalAuthority : NormativeSourceClass

sourceFamilyFor : NormativeSourceClass → Ingest.SourceFamily
sourceFamilyFor normativeDocument = Ingest.document
sourceFamilyFor normativeLegalAuthority = Ingest.legalAuthority

record BoundedNormativeDocsetContract : Set where
  constructor bounded-normative-docset-contract
  field
    docsetReference : String
    maximumDocuments : Nat
    maximumExtractedCharactersPerDocument : Nat
    maximumRegionAssignmentsPerDocument : Nat
    extractorReference : String

    sourceRevisionRequired : Bool
    sourceRevisionRequiredIsTrue :
      sourceRevisionRequired ≡ true

    sourceDigestRequired : Bool
    sourceDigestRequiredIsTrue :
      sourceDigestRequired ≡ true

    sourceArtifactRemainsCanonicalIdentity : Bool
    sourceArtifactRemainsCanonicalIdentityIsTrue :
      sourceArtifactRemainsCanonicalIdentity ≡ true

    derivedTextDigestRequired : Bool
    derivedTextDigestRequiredIsTrue :
      derivedTextDigestRequired ≡ true

    networkDuringExtractionAllowed : Bool
    networkDuringExtractionAllowedIsFalse :
      networkDuringExtractionAllowed ≡ false

    implicitOCRAllowed : Bool
    implicitOCRAllowedIsFalse :
      implicitOCRAllowed ≡ false

    extractionCandidateOnly : Bool
    extractionCandidateOnlyIsTrue :
      extractionCandidateOnly ≡ true

    extractionCreatesSemanticAuthority : Bool
    extractionCreatesSemanticAuthorityIsFalse :
      extractionCreatesSemanticAuthority ≡ false

    extractionCreatesLegalAuthority : Bool
    extractionCreatesLegalAuthorityIsFalse :
      extractionCreatesLegalAuthority ≡ false

    extractionCreatesClaimTruth : Bool
    extractionCreatesClaimTruthIsFalse :
      extractionCreatesClaimTruth ≡ false

    extractionPromotesApplicability : Bool
    extractionPromotesApplicabilityIsFalse :
      extractionPromotesApplicability ≡ false

    extractionClosesConsumer : Bool
    extractionClosesConsumerIsFalse :
      extractionClosesConsumer ≡ false

open BoundedNormativeDocsetContract public

mkBoundedNormativeDocsetContract :
  String →
  Nat →
  Nat →
  Nat →
  String →
  BoundedNormativeDocsetContract
mkBoundedNormativeDocsetContract
  docset
  documentBound
  characterBound
  assignmentBound
  extractor =
  bounded-normative-docset-contract
    docset
    documentBound
    characterBound
    assignmentBound
    extractor
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Ingestion receipt.
--
-- The generic source weld remains the canonical source identity.
-- The text materialisation receipt remains the canonical extraction carrier.
------------------------------------------------------------------------

record NormativeDocumentIngestionReceipt
    (contract : BoundedNormativeDocsetContract) : Set where
  constructor normative-document-ingestion-receipt
  field
    sourceClass : NormativeSourceClass
    compiledSource : Weld.GenericCompiledSource

    sourceFamilyMatchesClass :
      Weld.family compiledSource ≡ sourceFamilyFor sourceClass

    sourceRevisionReference : String
    sourceRevisionMatchesCanonical :
      sourceRevisionReference
      ≡ Canonical.revisionSourceRevisionRef (Weld.revision compiledSource)

    sourceDigestReference : String
    sourceDigestMatchesCanonical :
      sourceDigestReference
      ≡ Canonical.revisionContentDigestRef (Weld.revision compiledSource)

    documentOrdinal : Nat
    documentOrdinalWithinBound :
      suc documentOrdinal ≤ maximumDocuments contract

    materialisation : Text.DocumentTextMaterialisationReceipt

    materialisationSourceDigestMatchesCanonical :
      Text.sourceArtifactSha256 materialisation
      ≡ sourceDigestReference

open NormativeDocumentIngestionReceipt public

------------------------------------------------------------------------
-- Extraction receipt.
--
-- The extraction must consume the admitted source.
-- It must remain within the declared character and assignment budgets.
-- Lossless compilation preserves parser residuals instead of deleting them.
------------------------------------------------------------------------

record BoundedNormativeExtractionReceipt
    {contract : BoundedNormativeDocsetContract}
    (ingestion : NormativeDocumentIngestionReceipt contract) : Set₁ where
  constructor bounded-normative-extraction-receipt
  field
    extractionReference : String

    derivedTextDigestReference : String
    derivedTextDigestMatchesMaterialisation :
      derivedTextDigestReference
      ≡ Text.extractedTextSha256
          (NormativeDocumentIngestionReceipt.materialisation ingestion)

    extractedCharacterCountWithinBound :
      Text.extractedCharacterCount
        (NormativeDocumentIngestionReceipt.materialisation ingestion)
      ≤ maximumExtractedCharactersPerDocument contract

    compilation :
      Weld.LosslessCompilationReceipt
        (NormativeDocumentIngestionReceipt.compiledSource ingestion)

    regionAssignmentCountWithinBound :
      length (Weld.assignments compilation)
      ≤ maximumRegionAssignmentsPerDocument contract

    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse :
      createsLegalAuthority ≡ false

    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

    promotesApplicability : Bool
    promotesApplicabilityIsFalse :
      promotesApplicability ≡ false

    closesConsumer : Bool
    closesConsumerIsFalse :
      closesConsumer ≡ false

open BoundedNormativeExtractionReceipt public

------------------------------------------------------------------------
-- Existing canonical boundaries remain selected.
------------------------------------------------------------------------

selectedGenericSourceBoundary : Ingest.GenericSourceCompilationBoundary
selectedGenericSourceBoundary =
  Ingest.canonicalGenericSourceCompilationBoundary

selectedDocumentTextBoundary : Text.DocumentTextMaterialisationBoundary
selectedDocumentTextBoundary =
  Text.canonicalDocumentTextMaterialisationBoundary

selectedJudgmentCandidateBoundary :
  Judgment.CanonicalJudgmentCitationCandidateBoundary
selectedJudgmentCandidateBoundary =
  Judgment.canonicalCanonicalJudgmentCitationCandidateBoundary

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data IngestionCreatesSemanticAuthority : Set where
data ExtractionCreatesLegalAuthority : Set where
data ExtractionCreatesClaimTruth : Set where
data ExtractionPromotesApplicability : Set where
data ExtractionClosesConsumer : Set where
data ExtractionCandidateBecomesCurrentAuthority : Set where
data BoundExceededMayStillSucceed : Set where
data ImplicitOCRMayBypassMaterialisationReceipt : Set where

ingestionDoesNotCreateSemanticAuthority :
  IngestionCreatesSemanticAuthority → ⊥
ingestionDoesNotCreateSemanticAuthority ()

extractionDoesNotCreateLegalAuthority :
  ExtractionCreatesLegalAuthority → ⊥
extractionDoesNotCreateLegalAuthority ()

extractionDoesNotCreateClaimTruth :
  ExtractionCreatesClaimTruth → ⊥
extractionDoesNotCreateClaimTruth ()

extractionDoesNotPromoteApplicability :
  ExtractionPromotesApplicability → ⊥
extractionDoesNotPromoteApplicability ()

extractionDoesNotCloseConsumer :
  ExtractionClosesConsumer → ⊥
extractionDoesNotCloseConsumer ()

candidateDoesNotBecomeCurrentAuthority :
  ExtractionCandidateBecomesCurrentAuthority → ⊥
candidateDoesNotBecomeCurrentAuthority ()

boundExceededFailsClosed :
  BoundExceededMayStillSucceed → ⊥
boundExceededFailsClosed ()

implicitOCRDoesNotBypassMaterialisation :
  ImplicitOCRMayBypassMaterialisationReceipt → ⊥
implicitOCRDoesNotBypassMaterialisation ()

judgmentCandidateExtractionStillDoesNotCloseConsumer :
  Judgment.ExtractionAutomaticallyConsumerClosure → ⊥
judgmentCandidateExtractionStillDoesNotCloseConsumer =
  Judgment.extractionDoesNotBecomeConsumerClosure

genericCandidateInterpretationStillDoesNotDetermineTruth :
  Ingest.CandidateInterpretationDeterminesTruth → ⊥
genericCandidateInterpretationStillDoesNotDetermineTruth =
  Ingest.candidateInterpretationDoesNotDetermineTruth

textMaterialisationStillDoesNotCreateSemanticAuthority :
  Text.TextMaterialisationCreatesSemanticAuthority → ⊥
textMaterialisationStillDoesNotCreateSemanticAuthority =
  Text.textMaterialisationDoesNotCreateSemanticAuthority

------------------------------------------------------------------------
-- Canonical boundary summary.
------------------------------------------------------------------------

record NormativeDocsetIngestionExtractionBoundary : Set where
  constructor normative-docset-ingestion-extraction-boundary
  field
    boundedDocumentCountRequired : Bool
    boundedDocumentCountRequiredIsTrue :
      boundedDocumentCountRequired ≡ true

    boundedExtractedCharactersRequired : Bool
    boundedExtractedCharactersRequiredIsTrue :
      boundedExtractedCharactersRequired ≡ true

    boundedRegionAssignmentsRequired : Bool
    boundedRegionAssignmentsRequiredIsTrue :
      boundedRegionAssignmentsRequired ≡ true

    exactRevisionAndDigestRequired : Bool
    exactRevisionAndDigestRequiredIsTrue :
      exactRevisionAndDigestRequired ≡ true

    explicitMaterialisationRequired : Bool
    explicitMaterialisationRequiredIsTrue :
      explicitMaterialisationRequired ≡ true

    losslessCompilationRequired : Bool
    losslessCompilationRequiredIsTrue :
      losslessCompilationRequired ≡ true

    implicitOCRPermitted : Bool
    implicitOCRPermittedIsFalse :
      implicitOCRPermitted ≡ false

    extractionCreatesAuthority : Bool
    extractionCreatesAuthorityIsFalse :
      extractionCreatesAuthority ≡ false

    extractionCreatesTruth : Bool
    extractionCreatesTruthIsFalse :
      extractionCreatesTruth ≡ false

    extractionCreatesApplicability : Bool
    extractionCreatesApplicabilityIsFalse :
      extractionCreatesApplicability ≡ false

    extractionCreatesConsumerClosure : Bool
    extractionCreatesConsumerClosureIsFalse :
      extractionCreatesConsumerClosure ≡ false

open NormativeDocsetIngestionExtractionBoundary public

canonicalNormativeDocsetIngestionExtractionBoundary :
  NormativeDocsetIngestionExtractionBoundary
canonicalNormativeDocsetIngestionExtractionBoundary =
  normative-docset-ingestion-extraction-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
