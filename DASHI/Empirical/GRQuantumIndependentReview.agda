module DASHI.Empirical.GRQuantumIndependentReview where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- External review and replication receipts.
--
-- Repository authors may prepare packets and answer findings, but they cannot
-- self-inhabit the independent sign-off fields below.

data ReviewRole : Set where
  mathematicalReviewer : ReviewRole
  physicsReviewer : ReviewRole
  replicationReviewerRole : ReviewRole

record ReviewerIdentity : Set where
  constructor reviewer-identity
  field
    stableIdentifier : String
    displayName : String
    affiliation : String
    expertise : List String
    contactOrProfile : String
open ReviewerIdentity public

record IndependenceDeclaration : Set where
  constructor independence-declaration
  field
    reviewer : ReviewerIdentity
    noRepositoryAuthorship : Bool
    noRepositoryAuthorshipIsTrue : noRepositoryAuthorship ≡ true
    noRecentDirectCollaboration : Bool
    noRecentDirectCollaborationIsTrue :
      noRecentDirectCollaboration ≡ true
    noUndisclosedFinancialConflict : Bool
    noUndisclosedFinancialConflictIsTrue :
      noUndisclosedFinancialConflict ≡ true
    noSupervisoryDependency : Bool
    noSupervisoryDependencyIsTrue : noSupervisoryDependency ≡ true
    conflictsAndRelationships : List String
    signedDeclarationReference : String
open IndependenceDeclaration public

record ReviewFinding : Set where
  constructor review-finding
  field
    findingIdentifier : String
    severity : String
    affectedModuleOrClaim : String
    description : String
    requestedEvidenceOrChange : String
    resolutionReference : String
    resolved : Bool
open ReviewFinding public

record SignedReview (role : ReviewRole) : Set₁ where
  field
    reviewer : ReviewerIdentity
    independence : IndependenceDeclaration
    reviewedCommit : String
    reviewedArtifactHashes : List String
    reviewProtocolVersion : String
    scope : List String
    exclusions : List String
    findings : List ReviewFinding

    ReviewAcceptance : Set
    acceptance : ReviewAcceptance
    allBlockingFindingsResolved : Set
    allBlockingFindingsResolvedProof : allBlockingFindingsResolved
    noClaimExceedsReviewedEvidence : Set
    noClaimExceedsReviewedEvidenceProof : noClaimExceedsReviewedEvidence

    signedReviewReference : String
    reviewDate : String
open SignedReview public

record ReplicationReceipt : Set₁ where
  field
    replicationLead : ReviewerIdentity
    independence : IndependenceDeclaration
    sourceCommit : String
    environmentManifest : List String
    datasetManifest : List String
    commandManifest : List String
    expectedArtifactHashes : List String
    observedArtifactHashes : List String
    numericalTolerancePolicy : String

    ReproductionAgreement : Set
    reproductionAgreementProof : ReproductionAgreement
    negativeAndFailureCasesReproduced : Set
    negativeAndFailureCasesReproducedProof :
      negativeAndFailureCasesReproduced
    noPrivateAuthorOnlyInputs : Set
    noPrivateAuthorOnlyInputsProof : noPrivateAuthorOnlyInputs

    replicationReportReference : String
    replicationDate : String
open ReplicationReceipt public

record IndependentGRQuantumReviewPackage : Set₁ where
  field
    mathematics : SignedReview mathematicalReviewer
    physics : SignedReview physicsReviewer
    replication : ReplicationReceipt

    mathematicsAndPhysicsReviewersDistinct : Set
    mathematicsAndPhysicsReviewersDistinctProof :
      mathematicsAndPhysicsReviewersDistinct
    reviewersIndependentOfReplicationLead : Set
    reviewersIndependentOfReplicationLeadProof :
      reviewersIndependentOfReplicationLead
    reviewedCommitMatchesReplicatedCommit : Set
    reviewedCommitMatchesReplicatedCommitProof :
      reviewedCommitMatchesReplicatedCommit
    allConflictsPubliclyDisclosed : Set
    allConflictsPubliclyDisclosedProof : allConflictsPubliclyDisclosed
open IndependentGRQuantumReviewPackage public

------------------------------------------------------------------------
-- Canonical review request packet.  It is a request, not a signed review.

record ReviewRequestPacket : Set where
  constructor review-request-packet
  field
    mathematicsScope : List String
    physicsScope : List String
    replicationScope : List String
    requiredCommitPin : String
    requiredArtifactPinning : String
    requiredConflictDisclosure : String
    mathematicsReviewCompleted : Bool
    mathematicsReviewCompletedIsFalse : mathematicsReviewCompleted ≡ false
    physicsReviewCompleted : Bool
    physicsReviewCompletedIsFalse : physicsReviewCompleted ≡ false
    replicationCompleted : Bool
    replicationCompletedIsFalse : replicationCompleted ≡ false
open ReviewRequestPacket public

canonicalReviewRequestPacket : ReviewRequestPacket
canonicalReviewRequestPacket =
  review-request-packet
    ("Agda theorem dependencies and absence of hidden postulates"
      ∷ "finite/model versus continuum claim boundaries"
      ∷ "Clifford/Spin, CCR, Einstein, constraint and UV proof obligations"
      ∷ [])
    ("observable correspondence and units"
      ∷ "accepted GR/QFT limit recovery"
      ∷ "benchmark fairness and numerical adequacy"
      ∷ "falsifiability and experimental feasibility"
      ∷ [])
    ("fresh environment reproduction"
      ∷ "artifact hash verification"
      ∷ "negative gate and failure-case verification"
      ∷ "matched-quality rerun"
      ∷ [])
    "review must pin an immutable commit SHA"
    "review must pin datasets, commands, environments and output hashes"
    "all authorship, collaboration, financial and supervisory relationships must be disclosed"
    false refl
    false refl
    false refl

record IndependentReviewBoundary : Set where
  constructor independent-review-boundary
  field
    reviewContractsImplemented : Bool
    reviewContractsImplementedIsTrue : reviewContractsImplemented ≡ true
    requestPacketImplemented : Bool
    requestPacketImplementedIsTrue : requestPacketImplemented ≡ true
    independentMathematicsReviewObtained : Bool
    independentMathematicsReviewObtainedIsFalse :
      independentMathematicsReviewObtained ≡ false
    independentPhysicsReviewObtained : Bool
    independentPhysicsReviewObtainedIsFalse :
      independentPhysicsReviewObtained ≡ false
    independentReplicationObtained : Bool
    independentReplicationObtainedIsFalse :
      independentReplicationObtained ≡ false
open IndependentReviewBoundary public

canonicalIndependentReviewBoundary : IndependentReviewBoundary
canonicalIndependentReviewBoundary =
  independent-review-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
