module DASHI.Core.AttributedPublicClaimExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ATTRIBUTED PUBLIC CLAIM / ARTIFACT PROVENANCE
--
-- Generalises the repository source-attribution discipline to journalism,
-- public statements, leaked/primary artifacts, parliamentary material and
-- official responses.  Attribution is not truth promotion.
------------------------------------------------------------------------

data PublicSourceRole : Set where
  primaryArtifact : PublicSourceRole
  authenticatedArtifactReport : PublicSourceRole
  participantStatement : PublicSourceRole
  oppositionAllegation : PublicSourceRole
  governmentResponse : PublicSourceRole
  parliamentaryRecord : PublicSourceRole
  journalisticReport : PublicSourceRole
  journalisticAnalysis : PublicSourceRole
  legalAuthorityReport : PublicSourceRole


data AuthenticationStatus : Set where
  directlyAuthenticated : AuthenticationStatus
  authenticatedByNamedReporter : AuthenticationStatus
  institutionallyPublished : AuthenticationStatus
  attributedButNotIndependentlyAuthenticated : AuthenticationStatus
  disputedAuthentication : AuthenticationStatus
  unresolvedAuthentication : AuthenticationStatus

record PublicArtifactCitation : Set where
  constructor public-artifact-citation
  field
    producerOrInstitution : String
    titleOrDescription : String
    publisherOrCustodian : String
    publicationYear : Nat
    stableReference : String
    exactLocator : String
    sourceRole : PublicSourceRole
    authenticationStatus : AuthenticationStatus
    boundedClaim : String

open PublicArtifactCitation public

record AttributedPublicClaim : Set where
  constructor attributed-public-claim
  field
    source : PublicArtifactCitation
    proposition : String
    sourceActuallyAssertsProposition : Bool
    sourceActuallyAssertsPropositionIsTrue :
      sourceActuallyAssertsProposition ≡ true
    propositionPromotedAsWorldTruth : Bool
    propositionPromotedAsWorldTruthIsFalse :
      propositionPromotedAsWorldTruth ≡ false

open AttributedPublicClaim public

record PublicClaimPromotionReceipt (claim : AttributedPublicClaim) : Set where
  constructor public-claim-promotion-receipt
  field
    selectedConsumer : String
    promotionBasis : String
    authenticityReviewed : Bool
    authenticityReviewedIsTrue : authenticityReviewed ≡ true
    propositionFitReviewed : Bool
    propositionFitReviewedIsTrue : propositionFitReviewed ≡ true
    contraryEvidenceReviewed : Bool
    contraryEvidenceReviewedIsTrue : contraryEvidenceReviewed ≡ true

open PublicClaimPromotionReceipt public

------------------------------------------------------------------------
-- Canonical no-collapse boundary.
------------------------------------------------------------------------

record PublicClaimBoundary : Set where
  constructor public-claim-boundary
  field
    attributedMeansTrue : Bool
    attributedMeansTrueIsFalse : attributedMeansTrue ≡ false
    authenticatedArtifactMeansInterpretationTrue : Bool
    authenticatedArtifactMeansInterpretationTrueIsFalse :
      authenticatedArtifactMeansInterpretationTrue ≡ false
    allegationMeansAdjudicated : Bool
    allegationMeansAdjudicatedIsFalse : allegationMeansAdjudicated ≡ false
    denialMeansDisproved : Bool
    denialMeansDisprovedIsFalse : denialMeansDisproved ≡ false

open PublicClaimBoundary public

canonicalPublicClaimBoundary : PublicClaimBoundary
canonicalPublicClaimBoundary =
  public-claim-boundary
    false refl
    false refl
    false refl
    false refl
