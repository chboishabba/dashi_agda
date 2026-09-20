module DASHI.Law.AustralianContractsReviewedHopCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)

import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.AustralianContractsLandscapeControllerExact as Landscape
import DASHI.Law.WaltonsReviewedPropositionPaymentExact as WaltonsReview
import DASHI.Law.SensibLawCitationUsePropositionExact as CitationUse
import DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballExact as OALC

------------------------------------------------------------------------
-- REVIEWED RECEIPT -> S14 ADAPTIVE HOP COMPILER
--
-- Review is the promotion gate.  A pinned source receipt alone may not invent
-- a contracts-trace authority identity.  Once an authority identity itself has
-- been explicitly reviewed, it may be appended as a candidate node.  Reviewed
-- proposition support may append a Supports edge to an already-known research
-- requirement.  Reviewed proposition-level citation use may append only the
-- narrow treatment classes represented by the contracts trace.
------------------------------------------------------------------------

data ReviewedHopResidualKind : Set where
  propositionContested : ReviewedHopResidualKind
  propositionContextOnly : ReviewedHopResidualKind
  supportingPropositionUnpaid : ReviewedHopResidualKind
  missingAuthorityIdentity : ReviewedHopResidualKind
  missingRequirementIdentity : ReviewedHopResidualKind
  unsupportedCitationUse : ReviewedHopResidualKind
  missingTreatmentIdentity : ReviewedHopResidualKind
  sourceIdentityReviewInvalid : ReviewedHopResidualKind
  sourceIdentityConflict : ReviewedHopResidualKind

record ReviewedContractAuthorityIdentity : Set₁ where
  constructor reviewedContractAuthorityIdentity
  field
    semanticReference : String
    label : String
    doctrine : Maybe Contracts.ContractDoctrine
    jurisdictionReference : String
    courtReference : Maybe String
    sourceRole : Contracts.ContractSourceRole
    authorityLevel : Contracts.ContractAuthorityLevel
    reviewerReference : String
    reviewerEvidenceReferences : List String
    sourceReceipt : OALC.PinnedOalcSourceReceipt
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false

open ReviewedContractAuthorityIdentity public

record ReviewedDocumentAlias : Set where
  constructor reviewedDocumentAlias
  field
    sourceDocumentReference : String
    semanticAuthorityReference : String
    sourceReceipt : OALC.PinnedOalcSourceReceipt
    exactSourceDocumentBindingReceipt : Set
    reviewerReference : String
    reviewerEvidenceReferences : List String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false

open ReviewedDocumentAlias public

data ReviewedHopCompilationDisposition : Set where
  appendCandidateDelta : ReviewedHopCompilationDisposition
  retainReviewedResidual : ReviewedHopCompilationDisposition

propositionDisposition :
  WaltonsReview.PropositionEvidenceDisposition →
  ReviewedHopCompilationDisposition
propositionDisposition WaltonsReview.supports = appendCandidateDelta
propositionDisposition WaltonsReview.contests = retainReviewedResidual
propositionDisposition WaltonsReview.contextOnly = retainReviewedResidual

supportsMayAppendCandidateDelta :
  propositionDisposition WaltonsReview.supports ≡ appendCandidateDelta
supportsMayAppendCandidateDelta = refl

contestsRemainResidual :
  propositionDisposition WaltonsReview.contests ≡ retainReviewedResidual
contestsRemainResidual = refl

contextOnlyRemainsResidual :
  propositionDisposition WaltonsReview.contextOnly ≡ retainReviewedResidual
contextOnlyRemainsResidual = refl

------------------------------------------------------------------------
-- Citation-use mapping matches the Rust reviewed-hop compiler exactly.
------------------------------------------------------------------------

citationUseTreatment :
  CitationUse.CitationUseStatus →
  Maybe Contracts.ContractTreatment
citationUseTreatment CitationUse.appliedUse = just Contracts.applies
citationUseTreatment CitationUse.followedUse = just Contracts.follows
citationUseTreatment CitationUse.distinguishedUse = just Contracts.distinguishes
citationUseTreatment CitationUse.adoptedUse = just Contracts.supports
citationUseTreatment CitationUse.reliedOnUse = just Contracts.supports
citationUseTreatment CitationUse.overruledUse = just Contracts.displaces
citationUseTreatment CitationUse.citedMention = nothing
citationUseTreatment CitationUse.quotedUse = nothing
citationUseTreatment CitationUse.criticisedUse = nothing
citationUseTreatment CitationUse.rejectedUse = nothing
citationUseTreatment CitationUse.partySubmissionUse = nothing
citationUseTreatment CitationUse.historicalBackgroundUse = nothing
citationUseTreatment CitationUse.citationUseUnresolved = nothing

followedUseMapsToFollows :
  citationUseTreatment CitationUse.followedUse ≡ just Contracts.follows
followedUseMapsToFollows = refl

appliedUseMapsToApplies :
  citationUseTreatment CitationUse.appliedUse ≡ just Contracts.applies
appliedUseMapsToApplies = refl

distinguishedUseMapsToDistinguishes :
  citationUseTreatment CitationUse.distinguishedUse
    ≡ just Contracts.distinguishes
distinguishedUseMapsToDistinguishes = refl

mereMentionDoesNotCreateTreatment :
  citationUseTreatment CitationUse.citedMention ≡ nothing
mereMentionDoesNotCreateTreatment = refl

quotationDoesNotCreateTreatment :
  citationUseTreatment CitationUse.quotedUse ≡ nothing
quotationDoesNotCreateTreatment = refl

criticismDoesNotForceTraceTreatment :
  citationUseTreatment CitationUse.criticisedUse ≡ nothing
criticismDoesNotForceTraceTreatment = refl

------------------------------------------------------------------------
-- Adaptive output remains the existing S14 delta type.
------------------------------------------------------------------------

ReviewedHopDelta : Set
ReviewedHopDelta = Landscape.ContractLandscapeExpansionDelta

data OalcReceiptAutomaticallyReviewedAuthorityIdentity : Set where
data ContestedReviewAutomaticallyPositiveTraceEdge : Set where
data ContextOnlyReviewAutomaticallyPositiveTraceEdge : Set where
data UnsupportedCitationUseAutomaticallyTraceTreatment : Set where
data MissingIdentityMayBeInventedByCompiler : Set where
data ReviewedHopCompilerAutomaticallyCurrentLaw : Set where
data ReviewedHopCompilerAutomaticallyLegalAuthority : Set where
data RawOalcDocumentAutomaticallyCanonicalTraceAlias : Set where
data ReviewedAliasMayRewriteSourceDocumentIdentity : Set where
data RejectedIdentityReviewMayCreateDocumentAlias : Set where
data ReviewedAliasMayIgnoreExactOalcVersion : Set where

oalcReceiptDoesNotBecomeReviewedIdentity :
  OalcReceiptAutomaticallyReviewedAuthorityIdentity → ⊥
oalcReceiptDoesNotBecomeReviewedIdentity ()

contestedReviewDoesNotCreatePositiveEdge :
  ContestedReviewAutomaticallyPositiveTraceEdge → ⊥
contestedReviewDoesNotCreatePositiveEdge ()

contextOnlyReviewDoesNotCreatePositiveEdge :
  ContextOnlyReviewAutomaticallyPositiveTraceEdge → ⊥
contextOnlyReviewDoesNotCreatePositiveEdge ()

unsupportedCitationUseDoesNotCreateTreatment :
  UnsupportedCitationUseAutomaticallyTraceTreatment → ⊥
unsupportedCitationUseDoesNotCreateTreatment ()

compilerCannotInventMissingIdentity :
  MissingIdentityMayBeInventedByCompiler → ⊥
compilerCannotInventMissingIdentity ()

reviewedHopCompilerDoesNotCreateCurrentLaw :
  ReviewedHopCompilerAutomaticallyCurrentLaw → ⊥
reviewedHopCompilerDoesNotCreateCurrentLaw ()

reviewedHopCompilerDoesNotCreateAuthority :
  ReviewedHopCompilerAutomaticallyLegalAuthority → ⊥
reviewedHopCompilerDoesNotCreateAuthority ()

rawOalcDocumentDoesNotCreateCanonicalAlias :
  RawOalcDocumentAutomaticallyCanonicalTraceAlias → ⊥
rawOalcDocumentDoesNotCreateCanonicalAlias ()

reviewedAliasDoesNotRewriteSourceIdentity :
  ReviewedAliasMayRewriteSourceDocumentIdentity → ⊥
reviewedAliasDoesNotRewriteSourceIdentity ()

rejectedIdentityReviewDoesNotCreateAlias :
  RejectedIdentityReviewMayCreateDocumentAlias → ⊥
rejectedIdentityReviewDoesNotCreateAlias ()

reviewedAliasMustBindExactOalcVersion :
  ReviewedAliasMayIgnoreExactOalcVersion → ⊥
reviewedAliasMustBindExactOalcVersion ()

record AustralianContractsReviewedHopCompilerBoundary : Set where
  constructor australianContractsReviewedHopCompilerBoundary
  field
    reviewedSourceIdentityMayAppendCandidateNode : Bool
    reviewedSourceIdentityMayAppendCandidateNodeIsTrue :
      reviewedSourceIdentityMayAppendCandidateNode ≡ true

    rawOalcReceiptMayAppendAuthorityNode : Bool
    rawOalcReceiptMayAppendAuthorityNodeIsFalse :
      rawOalcReceiptMayAppendAuthorityNode ≡ false

    reviewedSupportMayAppendSupportsEdge : Bool
    reviewedSupportMayAppendSupportsEdgeIsTrue :
      reviewedSupportMayAppendSupportsEdge ≡ true

    contestedReviewMayAppendPositiveEdge : Bool
    contestedReviewMayAppendPositiveEdgeIsFalse :
      contestedReviewMayAppendPositiveEdge ≡ false

    contextOnlyReviewMayAppendPositiveEdge : Bool
    contextOnlyReviewMayAppendPositiveEdgeIsFalse :
      contextOnlyReviewMayAppendPositiveEdge ≡ false

    unsupportedCitationUseRemainsResidual : Bool
    unsupportedCitationUseRemainsResidualIsTrue :
      unsupportedCitationUseRemainsResidual ≡ true

    missingAuthorityIdentityMayBeInvented : Bool
    missingAuthorityIdentityMayBeInventedIsFalse :
      missingAuthorityIdentityMayBeInvented ≡ false

    reviewedDocumentAliasMayResolveTreatmentIdentity : Bool
    reviewedDocumentAliasMayResolveTreatmentIdentityIsTrue :
      reviewedDocumentAliasMayResolveTreatmentIdentity ≡ true

    rawOalcDocumentCreatesCanonicalAlias : Bool
    rawOalcDocumentCreatesCanonicalAliasIsFalse :
      rawOalcDocumentCreatesCanonicalAlias ≡ false

    reviewedAliasRewritesSourceDocumentIdentity : Bool
    reviewedAliasRewritesSourceDocumentIdentityIsFalse :
      reviewedAliasRewritesSourceDocumentIdentity ≡ false

    rejectedIdentityReviewMayCreateDocumentAlias : Bool
    rejectedIdentityReviewMayCreateDocumentAliasIsFalse :
      rejectedIdentityReviewMayCreateDocumentAlias ≡ false

    reviewedAliasBindsExactOalcVersion : Bool
    reviewedAliasBindsExactOalcVersionIsTrue :
      reviewedAliasBindsExactOalcVersion ≡ true

    reviewedHopFeedsExistingAdaptiveDelta : Bool
    reviewedHopFeedsExistingAdaptiveDeltaIsTrue :
      reviewedHopFeedsExistingAdaptiveDelta ≡ true

    compilerCreatesCurrentLawConclusion : Bool
    compilerCreatesCurrentLawConclusionIsFalse :
      compilerCreatesCurrentLawConclusion ≡ false

    compilerCreatesLegalAuthority : Bool
    compilerCreatesLegalAuthorityIsFalse :
      compilerCreatesLegalAuthority ≡ false

canonicalAustralianContractsReviewedHopCompilerBoundary :
  AustralianContractsReviewedHopCompilerBoundary
canonicalAustralianContractsReviewedHopCompilerBoundary =
  australianContractsReviewedHopCompilerBoundary
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
