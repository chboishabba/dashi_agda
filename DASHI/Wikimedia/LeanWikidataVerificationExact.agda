module DASHI.Wikimedia.LeanWikidataVerificationExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.AristotleLeanMachineAttributionExact as Attribution
open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact

------------------------------------------------------------------------
-- JMD LEAN / WIKIDATA VERIFICATION STATUS
--
-- The Lean machine reports independently on encoding, import correspondence,
-- elaboration/typechecking, kernel checking, freshness, object/relation
-- alignment and report generation.  No coordinate is promoted into another.
------------------------------------------------------------------------

data EncodingStatus : Set where
  notEncoded : EncodingStatus
  encoded : EncodingStatus

data ImportStatus : Set where
  importNotChecked : ImportStatus
  importFaithfullyRepresented : ImportStatus
  importMismatch : ImportStatus
  importBlocked : ImportStatus

data CheckStatus : Set where
  checkNotRun : CheckStatus
  checkPassed : CheckStatus
  checkFailed : CheckStatus
  checkBlocked : CheckStatus

data ObjectAlignmentStatus : Set where
  exactSameObject : ObjectAlignmentStatus
  sameObjectDifferentRepresentation : ObjectAlignmentStatus
  relatedObject : ObjectAlignmentStatus
  wrongObject : ObjectAlignmentStatus
  objectAmbiguous : ObjectAlignmentStatus
  objectUnresolved : ObjectAlignmentStatus

data RelationAlignmentStatus : Set where
  relationAligned : RelationAlignmentStatus
  relationRelated : RelationAlignmentStatus
  relationWrongType : RelationAlignmentStatus
  relationAmbiguous : RelationAlignmentStatus
  relationUnresolved : RelationAlignmentStatus

data PublicationStatus : Set where
  reportNotGenerated : PublicationStatus
  reportGenerated : PublicationStatus
  reportGenerationFailed : PublicationStatus

record LeanVerificationReceipt : Set where
  constructor leanVerificationReceipt
  field
    verificationObservation : WorldObservation
    encodingStatus : EncodingStatus
    importStatus : ImportStatus
    elaborationStatus : CheckStatus
    kernelStatus : CheckStatus
    objectAlignment : ObjectAlignmentStatus
    relationAlignment : RelationAlignmentStatus
    proofOrQueryReference : String
    machineRuntimeReference : String
    publicationStatus : PublicationStatus
    summaryArtifactReference : String
    verificationCreatesWorldTruth : Bool
    verificationCreatesLegalAuthority : Bool
    verificationCreatesAgdaProof : Bool

open LeanVerificationReceipt public

------------------------------------------------------------------------
-- PROOF-DEBT ROUTER PROJECTION
------------------------------------------------------------------------

data MathematicalStatus : Set where
  mathematicalUnencoded : MathematicalStatus
  mathematicalEncoded : MathematicalStatus
  mathematicalDerived : MathematicalStatus

data StatementStatus : Set where
  statementUnresolved : StatementStatus
  exactStatementKnown : StatementStatus
  statementNeedsRefinement : StatementStatus

data CertificationStatus : Set where
  certificationNotRun : CertificationStatus
  leanKernelPassed : CertificationStatus
  leanKernelFailed : CertificationStatus
  certificationBlocked : CertificationStatus

data AttachmentStatus : Set where
  exactAttachment : AttachmentStatus
  representationEquivalentAttachment : AttachmentStatus
  relatedAttachment : AttachmentStatus
  wrongAttachment : AttachmentStatus
  ambiguousAttachment : AttachmentStatus
  unresolvedAttachment : AttachmentStatus

data ProofDebtPublicationStatus : Set where
  publicationNotGenerated : ProofDebtPublicationStatus
  csvGenerated : ProofDebtPublicationStatus
  summaryGenerated : ProofDebtPublicationStatus
  publicationFailed : ProofDebtPublicationStatus

record RelationProofDebtStatus : Set where
  constructor relationProofDebtStatus
  field
    relationStatusReference : String
    mathematicalStatus : MathematicalStatus
    statementStatus : StatementStatus
    certificationStatus : CertificationStatus
    proofDebtFreshnessStatus : FreshnessStatus
    attachmentStatus : AttachmentStatus
    proofDebtPublicationStatus : ProofDebtPublicationStatus

open RelationProofDebtStatus public

record ImportFaithfulnessReceipt : Set where
  constructor importFaithfulnessReceipt
  field
    retrievedObservation : WorldObservation
    importedStatementReference : String
    importerReference : String
    importStatusObserved : ImportStatus
    importFaithfulnessCreatesWorldTruth : Bool
    importFaithfulnessCreatesAuthority : Bool

open ImportFaithfulnessReceipt public

record LeanKernelReceipt : Set where
  constructor leanKernelReceipt
  field
    premiseSetReference : String
    formalStatementReference : String
    proofOrQueryReference : String
    machineRuntimeReference : String
    kernelCheckStatus : CheckStatus
    sourceRevisionReference : String
    kernelCreatesWorldTruth : Bool
    kernelCreatesLegalAuthority : Bool
    kernelCreatesAgdaProof : Bool

open LeanKernelReceipt public

data FetchedClaimEqualsImportedAssertion : Set where
data ImportedAssertionEqualsDerivedTheorem : Set where
data ImportFaithfulnessImpliesWorldTruth : Set where
data KernelPassedImpliesFreshSource : Set where
data ReportGeneratedImpliesKernelPassed : Set where
data LeanKernelReceiptEqualsAgdaProof : Set where
data SameObjectAlignmentImpliesRelationTruth : Set where
data CertificationStatusDeterminesFreshness : Set where
data PublicationStatusDeterminesCertification : Set where

data AttachmentStatusDeterminesWorldTruth : Set where

fetchedDoesNotEqualImported : FetchedClaimEqualsImportedAssertion → ⊥
fetchedDoesNotEqualImported ()

importedDoesNotEqualDerived : ImportedAssertionEqualsDerivedTheorem → ⊥
importedDoesNotEqualDerived ()

importFaithfulnessDoesNotCreateWorldTruth :
  ImportFaithfulnessImpliesWorldTruth → ⊥
importFaithfulnessDoesNotCreateWorldTruth ()

kernelPassedDoesNotImplyFreshSource : KernelPassedImpliesFreshSource → ⊥
kernelPassedDoesNotImplyFreshSource ()

reportGeneratedDoesNotImplyKernelPassed :
  ReportGeneratedImpliesKernelPassed → ⊥
reportGeneratedDoesNotImplyKernelPassed ()

leanKernelReceiptDoesNotBecomeAgdaProof : LeanKernelReceiptEqualsAgdaProof → ⊥
leanKernelReceiptDoesNotBecomeAgdaProof ()

sameObjectAlignmentDoesNotCreateRelationTruth :
  SameObjectAlignmentImpliesRelationTruth → ⊥
sameObjectAlignmentDoesNotCreateRelationTruth ()

certificationDoesNotDetermineFreshness : CertificationStatusDeterminesFreshness → ⊥
certificationDoesNotDetermineFreshness ()

publicationDoesNotDetermineCertification : PublicationStatusDeterminesCertification → ⊥
publicationDoesNotDetermineCertification ()

attachmentDoesNotDetermineWorldTruth : AttachmentStatusDeterminesWorldTruth → ⊥
attachmentDoesNotDetermineWorldTruth ()

------------------------------------------------------------------------
-- Exact source owner for this verification ABI.
------------------------------------------------------------------------

jmdLeanMachineAttributedSource : Source.AttributedSource
jmdLeanMachineAttributedSource = Attribution.jmdLeanArchiveSource
