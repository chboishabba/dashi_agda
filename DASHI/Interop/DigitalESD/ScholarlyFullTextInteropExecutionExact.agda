module DASHI.Interop.DigitalESD.ScholarlyFullTextInteropExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.DigitalESD.ScholarlyFullTextCrossPollinationExact as X

------------------------------------------------------------------------
-- THIN WRAPPER EXECUTION RECEIPT
--
-- Runtime owner:
--   interop_scripts/digital_esd/scholarly_fulltext.py
--
-- This owner binds one wrapper run to the cross-pollination contract.  It does
-- not certify the external parser's scientific correctness; it only records
-- exact request/output identity, same-object reconciliation and non-promotion.
------------------------------------------------------------------------

crossPollinationAuthority : X.ScholarlyFullTextCrossPollinationBoundary
crossPollinationAuthority = X.canonicalScholarlyFullTextCrossPollinationBoundary

record ScholarlyFullTextInteropExecutionReceipt : Set where
  constructor scholarly-fulltext-interop-execution-receipt
  field
    wrapperReference : String
    wrapperVersionReference : String
    agdaContractReference : String

    requestArtifactReference : String
    requestArtifactSha256 : String
    parserOutputArtifactReference : String
    parserOutputArtifactSha256 : String
    verifiedOutputArtifactReference : String
    verifiedOutputArtifactSha256 : String

    preparedRequestCount : Nat
    verifiedBundleCount : Nat
    missingRequestCount : Nat
    documentNodeCount : Nat
    studyFacetCount : Nat

    sourceIdentityReconciled : Bool
    sourceIdentityReconciledIsTrue :
      sourceIdentityReconciled ≡ true

    sourceRevisionReconciled : Bool
    sourceRevisionReconciledIsTrue :
      sourceRevisionReconciled ≡ true

    contentDigestReconciled : Bool
    contentDigestReconciledIsTrue :
      contentDigestReconciled ≡ true

    documentAnchorsReconciled : Bool
    documentAnchorsReconciledIsTrue :
      documentAnchorsReconciled ≡ true

    studyFacetObservationsReconciled : Bool
    studyFacetObservationsReconciledIsTrue :
      studyFacetObservationsReconciled ≡ true

    candidateOnlyVerified : Bool
    candidateOnlyVerifiedIsTrue :
      candidateOnlyVerified ≡ true

    partialParseExplicit : Bool

    processExitCreatesReviewPayment : Bool
    processExitCreatesReviewPaymentIsFalse :
      processExitCreatesReviewPayment ≡ false

    verifiedBundleCreatesSourceTruth : Bool
    verifiedBundleCreatesSourceTruthIsFalse :
      verifiedBundleCreatesSourceTruth ≡ false

    verifiedBundleCreatesSourceAuditAdmission : Bool
    verifiedBundleCreatesSourceAuditAdmissionIsFalse :
      verifiedBundleCreatesSourceAuditAdmission ≡ false

open ScholarlyFullTextInteropExecutionReceipt public

record ScholarlyFullTextInteropExecutionBoundary : Set where
  constructor scholarly-fulltext-interop-execution-boundary
  field
    exactRequestArtifactRequired : Bool
    exactRequestArtifactRequiredIsTrue :
      exactRequestArtifactRequired ≡ true

    exactParserOutputArtifactRequired : Bool
    exactParserOutputArtifactRequiredIsTrue :
      exactParserOutputArtifactRequired ≡ true

    exactVerifiedArtifactRequired : Bool
    exactVerifiedArtifactRequiredIsTrue :
      exactVerifiedArtifactRequired ≡ true

    sourceRevisionDigestReconciliationRequired : Bool
    sourceRevisionDigestReconciliationRequiredIsTrue :
      sourceRevisionDigestReconciliationRequired ≡ true

    exactDocumentAnchorReconciliationRequired : Bool
    exactDocumentAnchorReconciliationRequiredIsTrue :
      exactDocumentAnchorReconciliationRequired ≡ true

    parserMayEmitReviewedEvidence : Bool
    parserMayEmitReviewedEvidenceIsFalse :
      parserMayEmitReviewedEvidence ≡ false

    partialParseMustBeExplicit : Bool
    partialParseMustBeExplicitIsTrue :
      partialParseMustBeExplicit ≡ true

    wrapperOwnsParserSemantics : Bool
    wrapperOwnsParserSemanticsIsFalse :
      wrapperOwnsParserSemantics ≡ false

open ScholarlyFullTextInteropExecutionBoundary public

canonicalScholarlyFullTextInteropExecutionBoundary :
  ScholarlyFullTextInteropExecutionBoundary
canonicalScholarlyFullTextInteropExecutionBoundary =
  scholarly-fulltext-interop-execution-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SuccessfulParserProcessCreatesReviewPayment : Set where
data VerifiedParserBundleCreatesSourceTruth : Set where
data VerifiedParserBundleCreatesSourceAuditAdmission : Set where
data PartialParseCreatesCompleteCorpusReceipt : Set where
data ReconciledDigestCreatesStudyTruth : Set where
data ParsedNodeCreatesReviewedObservation : Set where

successfulParserProcessDoesNotCreateReviewPayment :
  SuccessfulParserProcessCreatesReviewPayment → ⊥
successfulParserProcessDoesNotCreateReviewPayment ()

verifiedParserBundleDoesNotCreateSourceTruth :
  VerifiedParserBundleCreatesSourceTruth → ⊥
verifiedParserBundleDoesNotCreateSourceTruth ()

verifiedParserBundleDoesNotCreateSourceAuditAdmission :
  VerifiedParserBundleCreatesSourceAuditAdmission → ⊥
verifiedParserBundleDoesNotCreateSourceAuditAdmission ()

partialParseDoesNotCreateCompleteCorpusReceipt :
  PartialParseCreatesCompleteCorpusReceipt → ⊥
partialParseDoesNotCreateCompleteCorpusReceipt ()

reconciledDigestDoesNotCreateStudyTruth :
  ReconciledDigestCreatesStudyTruth → ⊥
reconciledDigestDoesNotCreateStudyTruth ()

parsedNodeDoesNotCreateReviewedObservation :
  ParsedNodeCreatesReviewedObservation → ⊥
parsedNodeDoesNotCreateReviewedObservation ()

scholarlyFullTextInteropExecutionReading : String
scholarlyFullTextInteropExecutionReading =
  "The Digital-ESD scholarly full-text wrapper is an application-side execution/reconciliation boundary around an external parser capability. Each run binds exact request, raw parser output and verified output artifacts by SHA-256; reconciles source identity, source revision, content digest, document anchors and study-facet EvidenceObservation candidates; and verifies candidate/non-promotion state. A successful parser process is not review/payment, a verified bundle is not source truth or SourceAuditAdmission, and a bounded partial parse may not be represented as a complete corpus parse."
