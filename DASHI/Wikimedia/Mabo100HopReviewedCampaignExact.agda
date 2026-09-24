module DASHI.Wikimedia.Mabo100HopReviewedCampaignExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboConsumerResidualDiagnosisExact as Diagnosis
import DASHI.Wikimedia.MaboDurableIdentityBaselineExact as Baseline
import DASHI.Wikimedia.MaboKnownIdentityResidualPaymentExact as Known
import DASHI.Wikimedia.MaboReviewedEvidencePaymentExact as Payment
import DASHI.Wikimedia.MaboReviewedContextFederationExact as Context

------------------------------------------------------------------------
-- ADAPTIVE REVIEW-DRIVEN MABO CAMPAIGN
--
-- The production recurrence is not a breadth-first 100-hop graph walk. The
-- graph walker remains an inspection/world-view reader. The campaign budget is
-- instead a bound on committed epistemic transitions:
--
--   Wᵢ
--   -> diagnose current world
--   -> rebuild current ProofFrontier
--   -> Pareto-select one residual/producer move
--   -> require the execution review only after selection
--   -> acquire one exact source manifestation
--   -> parse bounded context / assess world delta
--   -> persist payment / identity / lineage / reviewed context
--   -> Wᵢ₊₁
--   -> RE-DIAGNOSE BEFORE SELECTING AGAIN.
--
-- Thus traversal depth, adaptive campaign cycles, and durable novel identity
-- cardinality are three different coordinates. A precomputed sibling queue is
-- not the campaign scheduler.
------------------------------------------------------------------------

campaignExecutable : String
campaignExecutable =
  "cargo run -p sensiblaw-world-expansion-runtime --example mabo_100hop_recurrent_campaign -- [IDENTITY_REVIEW_TSV] [CONTEXT_REVIEW_TSV]"

campaignDiagnosisExecutable : String
campaignDiagnosisExecutable = Diagnosis.slrExecutable

worldViewHopBudget : Nat
worldViewHopBudget = Diagnosis.requestedHopBudget

campaignCycleBudget : Nat
campaignCycleBudget = 100

-- Compatibility name retained for downstream consumers. Its campaign meaning
-- is now the adaptive cycle budget, not graph traversal depth.
campaignHopBudget : Nat
campaignHopBudget = campaignCycleBudget

identityReviewManifestFormat : String
identityReviewManifestFormat =
  "representation_ref<TAB>identity_class_ref<TAB>review_ref"

contextReviewManifestFormat : String
contextReviewManifestFormat =
  "source_revision_ref<TAB>bounded_candidate_set_sha256<TAB>review_ref"

reviewManifestFormat : String
reviewManifestFormat = identityReviewManifestFormat

------------------------------------------------------------------------
-- BOUNDED REVIEWED-CONTEXT -> PROVIDER REPLAY
------------------------------------------------------------------------

record ReviewedRelationProviderReplay : Set where
  constructor reviewed-relation-provider-replay
  field
    reviewedRelationRoleReference : String
    providerPropertyReference : String

open ReviewedRelationProviderReplay public

providerReplay : Context.MaboContextProperty → ReviewedRelationProviderReplay
providerReplay property =
  reviewed-relation-provider-replay
    (Context.relationRole property)
    (Context.propertyId property)

p1001ProviderReplay : ReviewedRelationProviderReplay
p1001ProviderReplay = providerReplay Context.p1001

p710ProviderReplay : ReviewedRelationProviderReplay
p710ProviderReplay = providerReplay Context.p710

p4884ProviderReplay : ReviewedRelationProviderReplay
p4884ProviderReplay = providerReplay Context.p4884

p1594ProviderReplay : ReviewedRelationProviderReplay
p1594ProviderReplay = providerReplay Context.p1594

p4006ProviderReplay : ReviewedRelationProviderReplay
p4006ProviderReplay = providerReplay Context.p4006

record ReviewedCampaignBoundary : Set where
  constructor reviewed-campaign-boundary
  field
    reviewManifestRequired : Bool
    diagnosisProposalEqualsIdentityReview : Bool
    identityReviewEqualsPersistedPayment : Bool
    persistedPaymentEqualsNovelDurableAdmission : Bool
    knownIdentityPaymentCountsNovel : Bool
    missingCarrierAnalysisCreatesMissingValue : Bool
    externalKnowledgeComparisonCreatesIdentityReview : Bool
    semiFormalPresentationCreatesIdentityReview : Bool
    wrongTypeFailsClosed : Bool
    pinnedSourceManifestationRequired : Bool
    reviewedPaymentPersistsBeforeNovelCycle : Bool
    durableBaselineQuotientsKnownRepresentations : Bool
    boundedReviewedRelationReplaysExactProviderProperty : Bool
    sameObjectPaymentEqualsNewRelatedObject : Bool
    authorityFamilyRouteCreatesLegalAuthority : Bool
    traversalDepthEqualsCampaignCycle : Bool
    durableNovelIdentityCountEqualsCampaignCycle : Bool
    nextHopDependsOnPostAcquisitionAssessment : Bool
    precomputedSiblingQueueIsCampaignScheduler : Bool
    schedulerSelectionDependsOnReviewAvailability : Bool
    identityReviewEqualsOutgoingContextReview : Bool
    latestRevisionLookupEqualsAdmittedSourceManifestation : Bool
    nonNovelAliasCreatesDiscoveryLineage : Bool
    sourceExpansionReceiptCountsNovelIdentity : Bool
    sourceExpansionReceiptCanCloseZeroBoundedEdges : Bool
    campaignCandidateOnly : Bool
    campaignCreatesSemanticAuthority : Bool
    campaignApplicabilityPromoted : Bool
    campaignClaimTruthPromoted : Bool

open ReviewedCampaignBoundary public

canonicalReviewedCampaignBoundary : ReviewedCampaignBoundary
canonicalReviewedCampaignBoundary =
  reviewed-campaign-boundary
    true
    false
    false
    false
    false
    false
    false
    false
    true
    true
    true
    true
    true
    false
    false
    false
    false
    true
    false
    false
    false
    false
    false
    false
    true
    true
    false
    false
    false

------------------------------------------------------------------------
-- Reuse only the diagnosis owner's public boundary. The campaign does not
-- reach through its private import aliases merely to restate the same theorem.
------------------------------------------------------------------------

campaignDiagnosisExperimentDesignCannotCreateEvidence :
  Diagnosis.experimentDesignCreatesEvidence Diagnosis.canonicalDiagnosisBoundary ≡ false
campaignDiagnosisExperimentDesignCannotCreateEvidence = refl

campaignDiagnosisWrongTypeMayReject :
  Diagnosis.wrongTypeMayRejectConsumerMismatch Diagnosis.canonicalDiagnosisBoundary ≡ true
campaignDiagnosisWrongTypeMayReject = refl

campaignDiagnosisExternalComparisonCannotPay :
  Diagnosis.externalKnowledgeComparisonCreatesPayment Diagnosis.canonicalDiagnosisBoundary ≡ false
campaignDiagnosisExternalComparisonCannotPay = refl

campaignDiagnosisSemiFormalPresentationCannotPay :
  Diagnosis.semiFormalPresentationCreatesPayment Diagnosis.canonicalDiagnosisBoundary ≡ false
campaignDiagnosisSemiFormalPresentationCannotPay = refl

campaignDiagnosisFailedFactorisationMayDemandRepair :
  Diagnosis.failedFactorisationMayDemandObserverRepair Diagnosis.canonicalDiagnosisBoundary ≡ true
campaignDiagnosisFailedFactorisationMayDemandRepair = refl

------------------------------------------------------------------------
-- Existing payment/restart/context theorems remain authoritative.
------------------------------------------------------------------------

knownIdentityReviewDoesNotAdvanceNovelty :
  Known.advancesNovelIdentityCardinality Known.maboEddieKnownIdentityPayment ≡ false
knownIdentityReviewDoesNotAdvanceNovelty =
  Known.maboKnownIdentityDoesNotAdvanceNovelty

paymentDoesNotPromoteClaimTruth :
  Payment.paymentPromotesClaimTruth Payment.maboParticipantIdentityPayment ≡ false
paymentDoesNotPromoteClaimTruth = refl

baselineConflictsFailClosed :
  Baseline.representationConflictFailsClosed
    Baseline.canonicalMaboDurableIdentityBaselineBoundary ≡ true
baselineConflictsFailClosed = refl

p4006CandidateStillDoesNotCreateAuthority :
  Context.p4006AuthoritySourceCandidateCreatesAuthority ≡ false
p4006CandidateStillDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Campaign-stage non-collapse firewalls.
------------------------------------------------------------------------

data DiagnosisProposalEqualsIdentityReview : Set where
data IdentityReviewEqualsPersistedPayment : Set where
data PersistedPaymentEqualsNovelDurableAdmission : Set where
data MissingCarrierAnalysisManufacturesMissingValue : Set where
data ExternalKnowledgeComparisonEqualsIdentityReview : Set where
data SemiFormalPresentationEqualsIdentityReview : Set where
data SameObjectPaymentEqualsNewRelatedObject : Set where
data AuthorityFamilyRouteEqualsLegalAuthority : Set where
data BoundedProviderReplayEqualsGeneralSemanticInference : Set where
data TraversalDepthEqualsCampaignCycle : Set where
data DurableNovelIdentityCountEqualsCampaignCycle : Set where
data PrecomputedSiblingQueueEqualsAdaptiveScheduler : Set where
data IdentityReviewEqualsOutgoingContextReview : Set where
data LatestRevisionLookupEqualsAdmittedSourceManifestation : Set where
data NonNovelAliasEqualsDiscoveryLineage : Set where
data SourceExpansionReceiptEqualsNovelIdentity : Set where

diagnosisProposalDoesNotEqualIdentityReview :
  DiagnosisProposalEqualsIdentityReview → ⊥
diagnosisProposalDoesNotEqualIdentityReview ()

identityReviewDoesNotEqualPersistedPayment :
  IdentityReviewEqualsPersistedPayment → ⊥
identityReviewDoesNotEqualPersistedPayment ()

persistedPaymentDoesNotEqualNovelDurableAdmission :
  PersistedPaymentEqualsNovelDurableAdmission → ⊥
persistedPaymentDoesNotEqualNovelDurableAdmission ()

missingCarrierAnalysisDoesNotManufactureMissingValue :
  MissingCarrierAnalysisManufacturesMissingValue → ⊥
missingCarrierAnalysisDoesNotManufactureMissingValue ()

externalKnowledgeComparisonDoesNotEqualIdentityReview :
  ExternalKnowledgeComparisonEqualsIdentityReview → ⊥
externalKnowledgeComparisonDoesNotEqualIdentityReview ()

semiFormalPresentationDoesNotEqualIdentityReview :
  SemiFormalPresentationEqualsIdentityReview → ⊥
semiFormalPresentationDoesNotEqualIdentityReview ()

sameObjectPaymentDoesNotEqualNewRelatedObject :
  SameObjectPaymentEqualsNewRelatedObject → ⊥
sameObjectPaymentDoesNotEqualNewRelatedObject ()

authorityFamilyRouteDoesNotEqualLegalAuthority :
  AuthorityFamilyRouteEqualsLegalAuthority → ⊥
authorityFamilyRouteDoesNotEqualLegalAuthority ()

boundedProviderReplayDoesNotEqualGeneralSemanticInference :
  BoundedProviderReplayEqualsGeneralSemanticInference → ⊥
boundedProviderReplayDoesNotEqualGeneralSemanticInference ()

traversalDepthDoesNotEqualCampaignCycle :
  TraversalDepthEqualsCampaignCycle → ⊥
traversalDepthDoesNotEqualCampaignCycle ()

durableNovelIdentityCountDoesNotEqualCampaignCycle :
  DurableNovelIdentityCountEqualsCampaignCycle → ⊥
durableNovelIdentityCountDoesNotEqualCampaignCycle ()

precomputedSiblingQueueDoesNotEqualAdaptiveScheduler :
  PrecomputedSiblingQueueEqualsAdaptiveScheduler → ⊥
precomputedSiblingQueueDoesNotEqualAdaptiveScheduler ()

identityReviewDoesNotEqualOutgoingContextReview :
  IdentityReviewEqualsOutgoingContextReview → ⊥
identityReviewDoesNotEqualOutgoingContextReview ()

latestRevisionLookupDoesNotEqualAdmittedSourceManifestation :
  LatestRevisionLookupEqualsAdmittedSourceManifestation → ⊥
latestRevisionLookupDoesNotEqualAdmittedSourceManifestation ()

nonNovelAliasDoesNotEqualDiscoveryLineage :
  NonNovelAliasEqualsDiscoveryLineage → ⊥
nonNovelAliasDoesNotEqualDiscoveryLineage ()

sourceExpansionReceiptDoesNotEqualNovelIdentity :
  SourceExpansionReceiptEqualsNovelIdentity → ⊥
sourceExpansionReceiptDoesNotEqualNovelIdentity ()

------------------------------------------------------------------------
-- Source-written runtime contract only. No Cargo/Agda execution receipt is
-- manufactured by this owner.
------------------------------------------------------------------------

record ReviewedCampaignRuntimeContract : Set where
  constructor reviewed-campaign-runtime-contract
  field
    diagnosisExecutableReference : String
    campaignExecutableReference : String
    identityReviewManifestSyntax : String
    contextReviewManifestSyntax : String
    worldInspectionHopBudget : Nat
    maxAdaptiveCampaignCycles : Nat
    selectionOccursBeforeReviewLookup : Bool
    exactRevisionReacquisitionRequired : Bool
    latestLookupOnlyDiscoversRevisionCoordinate : Bool
    boundedContextPropertyReplayRequired : Bool
    outgoingContextNeedsDistinctReview : Bool
    candidateSetDigestBindsContextReview : Bool
    sourceExpansionReceiptRestartStable : Bool
    knownIdentityUsesNonNovelPaymentLane : Bool
    nonNovelAliasPersistenceRequired : Bool
    novelIdentityUsesIdentityCoherentRunner : Bool
    singleNovelRunnerInvocationBoundedToOneCycle : Bool
    reDiagnosisRequiredAfterCompletedCycle : Bool
    lineagePersistenceRequiredBeforeIdentityCommit : Bool
    executionObserved : Bool

open ReviewedCampaignRuntimeContract public

canonicalReviewedCampaignRuntimeContract : ReviewedCampaignRuntimeContract
canonicalReviewedCampaignRuntimeContract =
  reviewed-campaign-runtime-contract
    campaignDiagnosisExecutable
    campaignExecutable
    identityReviewManifestFormat
    contextReviewManifestFormat
    worldViewHopBudget
    campaignCycleBudget
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
