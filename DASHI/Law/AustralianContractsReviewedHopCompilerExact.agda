module DASHI.Law.AustralianContractsReviewedHopCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)

import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.AustralianContractsLandscapeControllerExact as Landscape
import DASHI.Law.WaltonsReviewedPropositionPaymentExact as WaltonsReview
import DASHI.Law.MannPatersonUnseenMatterExact as Mann
import DASHI.Law.SensibLawCitationUsePropositionExact as CitationUse
import DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballExact as OALC
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as ParetoSnowball
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet
import DASHI.Law.ReviewedTreatmentBundleSemanticDedupExact as Dedup
import DASHI.Law.ReviewedWorkFrontierClosureExact as Closure
import DASHI.Law.ConsumerDirectedLegalFollowAdequacyExact as Adequacy
import DASHI.Law.ConsumerAdequacyRuntimeTheoremBridgeExact as AdequacyBridge
import DASHI.Law.ClosedIsNotAdequateExact as ClosedNotAdequate
import DASHI.Law.GenericRecursiveLegalFollowCampaignExact as Recursive
import DASHI.Law.GenericReviewedDeltaCampaignKernelExact as Kernel

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

data ContractPropositionDisposition : Set where
  propositionSupports : ContractPropositionDisposition
  propositionContests : ContractPropositionDisposition
  propositionContextOnly : ContractPropositionDisposition

record ReviewedContractPropositionReceipt : Set where
  constructor reviewedContractPropositionReceipt
  field
    reviewReference : String
    authorityReference : String
    targetReference : String
    propositionReference : String
    sourceRevisionReference : String
    spanReference : String
    disposition : ContractPropositionDisposition
    reviewerReference : String
    reviewerEvidenceReferences : List String
    evidenceCoordinatePaid : Bool
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    createsCurrentLawConclusion : Bool
    createsCurrentLawConclusionIsFalse :
      createsCurrentLawConclusion ≡ false

open ReviewedContractPropositionReceipt public

waltonsDisposition :
  WaltonsReview.PropositionEvidenceDisposition →
  ContractPropositionDisposition
waltonsDisposition WaltonsReview.supports = propositionSupports
waltonsDisposition WaltonsReview.contests = propositionContests
waltonsDisposition WaltonsReview.contextOnly = propositionContextOnly

mannRepudiationReviewedPropositionFixture :
  ReviewedContractPropositionReceipt
mannRepudiationReviewedPropositionFixture =
  reviewedContractPropositionReceipt
    "review:mann:repudiation"
    "matter:au:hca:2019:32"
    "doctrine:au:contract:repudiation-termination"
    "prop:mann:repudiation-termination"
    "source:mann:revision"
    "case:mann#paragraph-1"
    propositionSupports
    "reviewer:fixture"
    ("evidence:mann:fixture" ∷ [])
    true
    true refl
    false refl
    false refl

data ReviewedHopCompilationDisposition : Set where
  appendCandidateDelta : ReviewedHopCompilationDisposition
  retainReviewedResidual : ReviewedHopCompilationDisposition

contractPropositionDisposition :
  ContractPropositionDisposition →
  ReviewedHopCompilationDisposition
contractPropositionDisposition propositionSupports = appendCandidateDelta
contractPropositionDisposition propositionContests = retainReviewedResidual
contractPropositionDisposition propositionContextOnly = retainReviewedResidual

propositionDisposition :
  WaltonsReview.PropositionEvidenceDisposition →
  ReviewedHopCompilationDisposition
propositionDisposition disposition =
  contractPropositionDisposition (waltonsDisposition disposition)

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

    genericReviewedPropositionCompilerIsDoctrineIndependent : Bool
    genericReviewedPropositionCompilerIsDoctrineIndependentIsTrue :
      genericReviewedPropositionCompilerIsDoctrineIndependent ≡ true

    waltonsUsesGenericReviewedPropositionCompiler : Bool
    waltonsUsesGenericReviewedPropositionCompilerIsTrue :
      waltonsUsesGenericReviewedPropositionCompiler ≡ true

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
    true refl
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


------------------------------------------------------------------------
-- TOE / fleet normalization.
--
-- The current problem is one formal residual lane:
--
-- retained primary source
--   -> reviewed source identity
--   -> reviewed proposition or treatment
--   -> candidate adaptive delta
--   -> recomputed residual frontier
--
-- No earlier carrier may skip a later review gate.
------------------------------------------------------------------------

reviewedContractsAuthorityBundle :
  Authority.AuthorityNonPromotionBundle
reviewedContractsAuthorityBundle =
  Authority.mkClosedAuthorityNonPromotionBundle
    "Australian contracts reviewed-hop compiler"

reviewedContractsAuthorityStillClosed :
  Authority.promotesAnyAuthority reviewedContractsAuthorityBundle ≡ false
reviewedContractsAuthorityStillClosed =
  Authority.promotesAnyAuthorityIsFalse reviewedContractsAuthorityBundle

reviewedContractsPromotesAnyAuthority : Bool
reviewedContractsPromotesAnyAuthority =
  Authority.promotesAnyAuthority reviewedContractsAuthorityBundle

reviewedContractsPromotesAnyAuthorityIsFalse :
  reviewedContractsPromotesAnyAuthority ≡ false
reviewedContractsPromotesAnyAuthorityIsFalse =
  reviewedContractsAuthorityStillClosed

reviewedContractsFleetTarget :
  Fleet.FleetFormalGapTargetReceipt
reviewedContractsFleetTarget =
  Fleet.canonicalFleetFormalGapTargetReceipt

reviewedContractsTargetsOnlyFormalGaps :
  Fleet.targetOnlyUnformalisedFormalGaps reviewedContractsFleetTarget ≡ true
reviewedContractsTargetsOnlyFormalGaps =
  Fleet.fleetTargetsOnlyUnformalisedFormalGaps

reviewedContractsDischargedFibresRemainDischarged :
  Fleet.dischargedCoreKnowledgeFibres reviewedContractsFleetTarget ≡ 584
reviewedContractsDischargedFibresRemainDischarged =
  Fleet.fleetRecordedDischargedCountIs584

reviewedContractsFormalGapBudgetIs58 :
  Fleet.unformalisedFormalGaps reviewedContractsFleetTarget ≡ 58
reviewedContractsFormalGapBudgetIs58 =
  Fleet.fleetRecordedUnformalisedGapCountIs58

reviewedContractsDischargedFibreCount : Nat
reviewedContractsDischargedFibreCount =
  Fleet.dischargedCoreKnowledgeFibres reviewedContractsFleetTarget

reviewedContractsDischargedFibreCountIs584 :
  reviewedContractsDischargedFibreCount ≡ 584
reviewedContractsDischargedFibreCountIs584 =
  reviewedContractsDischargedFibresRemainDischarged

reviewedContractsFormalGapCount : Nat
reviewedContractsFormalGapCount =
  Fleet.unformalisedFormalGaps reviewedContractsFleetTarget

reviewedContractsFormalGapCountIs58 :
  reviewedContractsFormalGapCount ≡ 58
reviewedContractsFormalGapCountIs58 =
  reviewedContractsFormalGapBudgetIs58

ReviewedContractsTOEZKPFrame : Set
ReviewedContractsTOEZKPFrame =
  ParetoSnowball.TOEZKPFrame

reviewedContractsZKPFrame :
  ReviewedContractsTOEZKPFrame
reviewedContractsZKPFrame =
  ParetoSnowball.toe-zkp-frame
    "O: close the reviewed legal-follow handoff from pinned Australian primary source to adaptive S14 residual recomputation"
    "R: reuse existing OALC, review, non-promotion, adaptive residual, Pareto, snowball, attribution and fleet-gap owners"
    "C: require reviewed source identity before canonical trace alias; require reviewed proposition or citation use before positive trace edge"
    "S: raw acquisition, lexical match, QID, citation occurrence, ranking and unresolved identity remain candidate or residual state"
    "L: one disjoint legal reviewed-hop lane; accepted hops append provenance and force a fresh frontier without freezing prior conclusions"
    "P: exact source revision and document identity exist; reviewer and evidence receipts exist; the 584 discharged fibres remain excluded"
    "G: preserve original source authors, DASHI theorem owners, Ibrahim ownership and meta-introspector attribution; ESD surfaces remain read-only"
    "F: output only candidate nodes or treatment/support edges plus explicit residuals; never legal authority or current-law conclusion"
    "verify duplicate search, exact identity binding, no shortcut promotion, residual preservation, TOE reachability, trust-escape scan and kernel check"
    false
    false
    false
    false

record ReviewedContractsMaxCutBoundary : Set where
  constructor reviewed-contracts-max-cut-boundary
  field
    rawSourceNeedsIdentityReview : Bool
    rawSourceNeedsIdentityReviewIsTrue :
      rawSourceNeedsIdentityReview ≡ true

    sourceIdentityNeedsExactRevisionBinding : Bool
    sourceIdentityNeedsExactRevisionBindingIsTrue :
      sourceIdentityNeedsExactRevisionBinding ≡ true

    propositionSupportNeedsReviewedPayment : Bool
    propositionSupportNeedsReviewedPaymentIsTrue :
      propositionSupportNeedsReviewedPayment ≡ true

    citationTreatmentNeedsReviewedUse : Bool
    citationTreatmentNeedsReviewedUseIsTrue :
      citationTreatmentNeedsReviewedUse ≡ true

    contestedAndContextRemainResidual : Bool
    contestedAndContextRemainResidualIsTrue :
      contestedAndContextRemainResidual ≡ true

    reviewedResidualsSurviveTrajectory : Bool
    reviewedResidualsSurviveTrajectoryIsTrue :
      reviewedResidualsSurviveTrajectory ≡ true

    acceptedHopForcesFrontierRecompute : Bool
    acceptedHopForcesFrontierRecomputeIsTrue :
      acceptedHopForcesFrontierRecompute ≡ true

    qidMayScheduleButCannotPromote : Bool
    qidMayScheduleButCannotPromoteIsTrue :
      qidMayScheduleButCannotPromote ≡ true

    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse :
      createsLegalAuthority ≡ false

    createsCurrentLawConclusion : Bool
    createsCurrentLawConclusionIsFalse :
      createsCurrentLawConclusion ≡ false

canonicalReviewedContractsMaxCutBoundary :
  ReviewedContractsMaxCutBoundary
canonicalReviewedContractsMaxCutBoundary =
  reviewed-contracts-max-cut-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl



------------------------------------------------------------------------
-- Current SLR runtime parity.
--
-- These are aliases to existing theorem owners.
-- This file does not duplicate their constructions.
------------------------------------------------------------------------

reviewedTreatmentDedupBoundary :
  Dedup.ReviewedTreatmentBundleBoundary
reviewedTreatmentDedupBoundary =
  Dedup.canonicalReviewedTreatmentBundleBoundary

reviewedWorkClosureBoundary :
  Closure.ReviewedWorkFrontierClosureBoundary
reviewedWorkClosureBoundary =
  Closure.canonicalReviewedWorkFrontierClosureBoundary

consumerLegalFollowAdequacyBoundary :
  Adequacy.ConsumerDirectedLegalFollowAdequacyBoundary
consumerLegalFollowAdequacyBoundary =
  Adequacy.canonicalConsumerDirectedLegalFollowAdequacyBoundary

consumerAdequacyRuntimeBridgeBoundary :
  AdequacyBridge.ConsumerAdequacyRuntimeTheoremBridgeBoundary
consumerAdequacyRuntimeBridgeBoundary =
  AdequacyBridge.canonicalConsumerAdequacyRuntimeTheoremBridgeBoundary

genericRecursiveCampaignBoundary :
  Recursive.GenericRecursiveCampaignBoundary
genericRecursiveCampaignBoundary =
  Recursive.canonicalGenericRecursiveCampaignBoundary

genericReviewedDeltaKernelBoundary :
  Kernel.GenericReviewedDeltaCampaignKernelBoundary
genericReviewedDeltaKernelBoundary =
  Kernel.canonicalGenericReviewedDeltaCampaignKernelBoundary

record ReviewedContractsRuntimeParityBoundary : Set where
  constructor reviewed-contracts-runtime-parity-boundary
  field
    corroboratingReviewUnitsMayDeduplicateToOneSemanticHop : Bool
    corroboratingReviewUnitsMayDeduplicateToOneSemanticHopIsTrue :
      corroboratingReviewUnitsMayDeduplicateToOneSemanticHop ≡ true

    allSupportingReviewProvenanceIsRetained : Bool
    allSupportingReviewProvenanceIsRetainedIsTrue :
      allSupportingReviewProvenanceIsRetained ≡ true

    unsupportedReviewedResidualsSurviveDeduplication : Bool
    unsupportedReviewedResidualsSurviveDeduplicationIsTrue :
      unsupportedReviewedResidualsSurviveDeduplication ≡ true

    paidIdentityWorkMayResurrectAsFreshSourceWork : Bool
    paidIdentityWorkMayResurrectAsFreshSourceWorkIsFalse :
      paidIdentityWorkMayResurrectAsFreshSourceWork ≡ false

    paidTreatmentWorkMayResurrectAsFreshTreatmentWork : Bool
    paidTreatmentWorkMayResurrectAsFreshTreatmentWorkIsFalse :
      paidTreatmentWorkMayResurrectAsFreshTreatmentWork ≡ false

    frontierClosureMeansFormalConsumerAdequacy : Bool
    frontierClosureMeansFormalConsumerAdequacyIsFalse :
      frontierClosureMeansFormalConsumerAdequacy ≡ false

    runtimeCoverageIsFormalFactorsThroughProof : Bool
    runtimeCoverageIsFormalFactorsThroughProofIsFalse :
      runtimeCoverageIsFormalFactorsThroughProof ≡ false

    theoremBackedAdequacyRequiresActualAdequateFor : Bool
    theoremBackedAdequacyRequiresActualAdequateForIsTrue :
      theoremBackedAdequacyRequiresActualAdequateFor ≡ true

    genericKernelAcceptsOnlyReviewedDelta : Bool
    genericKernelAcceptsOnlyReviewedDeltaIsTrue :
      genericKernelAcceptsOnlyReviewedDelta ≡ true

    genericKernelMayConvertRawSourceToReviewedDelta : Bool
    genericKernelMayConvertRawSourceToReviewedDeltaIsFalse :
      genericKernelMayConvertRawSourceToReviewedDelta ≡ false

    recursiveCampaignRecomputesAfterAcceptedHop : Bool
    recursiveCampaignRecomputesAfterAcceptedHopIsTrue :
      recursiveCampaignRecomputesAfterAcceptedHop ≡ true

    recursiveCampaignUsesFixedUpfrontQueue : Bool
    recursiveCampaignUsesFixedUpfrontQueueIsFalse :
      recursiveCampaignUsesFixedUpfrontQueue ≡ false

    recursiveResearchPriorityIsLegalTruthRank : Bool
    recursiveResearchPriorityIsLegalTruthRankIsFalse :
      recursiveResearchPriorityIsLegalTruthRank ≡ false

    recursiveCampaignIsBudgetBounded : Bool
    recursiveCampaignIsBudgetBoundedIsTrue :
      recursiveCampaignIsBudgetBounded ≡ true

    runtimeParityCreatesLegalAuthority : Bool
    runtimeParityCreatesLegalAuthorityIsFalse :
      runtimeParityCreatesLegalAuthority ≡ false

    runtimeParityCreatesCurrentLawConclusion : Bool
    runtimeParityCreatesCurrentLawConclusionIsFalse :
      runtimeParityCreatesCurrentLawConclusion ≡ false

canonicalReviewedContractsRuntimeParityBoundary :
  ReviewedContractsRuntimeParityBoundary
canonicalReviewedContractsRuntimeParityBoundary =
  reviewed-contracts-runtime-parity-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl

reviewedContractsDedupProvenanceOwnerProof :
  Dedup.allSupportingReviewUnitProvenanceRetained
    reviewedTreatmentDedupBoundary
  ≡ true
reviewedContractsDedupProvenanceOwnerProof =
  Dedup.allSupportingReviewUnitProvenanceRetainedIsTrue
    reviewedTreatmentDedupBoundary

reviewedContractsPaidTreatmentDoesNotResurrectOwnerProof :
  Closure.acceptedReviewedTreatmentMayReopenItselfAsFreshTreatment
    reviewedWorkClosureBoundary
  ≡ false
reviewedContractsPaidTreatmentDoesNotResurrectOwnerProof =
  Closure.acceptedReviewedTreatmentMayReopenItselfAsFreshTreatmentIsFalse
    reviewedWorkClosureBoundary

reviewedContractsFrontierClosedNotAdequateOwnerProof :
  Closure.currentFrontierClosedImpliesConsumerAdequacyProved
    reviewedWorkClosureBoundary
  ≡ false
reviewedContractsFrontierClosedNotAdequateOwnerProof =
  Closure.currentFrontierClosedImpliesConsumerAdequacyProvedIsFalse
    reviewedWorkClosureBoundary

reviewedContractsRuntimeCoverageNotFactorsThroughOwnerProof :
  Adequacy.runtimeCoverageReceiptIsFormalFactorsThroughProof
    consumerLegalFollowAdequacyBoundary
  ≡ false
reviewedContractsRuntimeCoverageNotFactorsThroughOwnerProof =
  Adequacy.runtimeCoverageReceiptIsFormalFactorsThroughProofIsFalse
    consumerLegalFollowAdequacyBoundary

reviewedContractsKernelReviewedOnlyOwnerProof :
  Kernel.kernelAcceptsOnlyReviewedDeltaInterface
    genericReviewedDeltaKernelBoundary
  ≡ true
reviewedContractsKernelReviewedOnlyOwnerProof =
  Kernel.kernelAcceptsOnlyReviewedDeltaInterfaceIsTrue
    genericReviewedDeltaKernelBoundary

reviewedContractsRecursiveRecomputeOwnerProof :
  Recursive.freshFrontierRecomputedAfterAcceptedHop
    genericRecursiveCampaignBoundary
  ≡ true
reviewedContractsRecursiveRecomputeOwnerProof =
  Recursive.freshFrontierRecomputedAfterAcceptedHopIsTrue
    genericRecursiveCampaignBoundary

