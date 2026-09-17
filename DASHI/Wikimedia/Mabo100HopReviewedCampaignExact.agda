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
-- REVIEW-DRIVEN 100-HOP MABO CAMPAIGN
--
-- This owner is deliberately downstream of the existing diagnosis surface.
-- It does not invent another planner, review ontology, proof-search system, or
-- evidence-payment calculus. The runtime shape is:
--
--   persisted 100-hop world
--   -> explicit consumer diagnosis / ProofResidual frontier
--   -> explicit operator identity-review manifest
--   -> pinned source reacquisition
--   -> reviewed SameObject payment
--   -> known-identity non-novel contraction OR identity-coherent novel cycle
--   -> durable lineage persistence
--   -> recurrence.
--
-- Proof search, experiment design, failed FactorsThrough, WrongType,
-- affected-subject/missing-carrier analysis, SFM, and Perplexity/external
-- comparison remain proposal/diagnostic routes inherited from Diagnosis.
------------------------------------------------------------------------

campaignExecutable : String
campaignExecutable =
  "cargo run -p sensiblaw-world-expansion-runtime --example mabo_100hop_recurrent_campaign -- [IDENTITY_REVIEW_TSV]"

campaignDiagnosisExecutable : String
campaignDiagnosisExecutable = Diagnosis.slrExecutable

campaignHopBudget : Nat
campaignHopBudget = Diagnosis.requestedHopBudget

reviewManifestFormat : String
reviewManifestFormat =
  "representation_ref<TAB>identity_class_ref<TAB>review_ref"

------------------------------------------------------------------------
-- BOUNDED REVIEWED-CONTEXT -> PROVIDER REPLAY
--
-- SLR persists the semantic reviewed role (participant, judge, overrules, ...)
-- in the latent-world relation rather than a free-standing property id.  The
-- production replay is allowed to recover a Wikidata property only because the
-- canonical federation owner already defines a finite one-to-one map for the
-- five reviewed Mabo properties.  This is not a general label -> property
-- inference rule and introduces no second property ontology here.
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

------------------------------------------------------------------------
-- Source-written runtime contract only. No Cargo/Agda execution receipt is
-- manufactured by this owner.
------------------------------------------------------------------------

record ReviewedCampaignRuntimeContract : Set where
  constructor reviewed-campaign-runtime-contract
  field
    diagnosisExecutableReference : String
    campaignExecutableReference : String
    reviewManifestSyntax : String
    maxHopBudget : Nat
    explicitReviewBeforeProviderIO : Bool
    exactRevisionReacquisitionRequired : Bool
    boundedContextPropertyReplayRequired : Bool
    knownIdentityUsesNonNovelPaymentLane : Bool
    novelIdentityUsesIdentityCoherentRunner : Bool
    lineagePersistenceRequiredBeforeCommit : Bool
    executionObserved : Bool

open ReviewedCampaignRuntimeContract public

canonicalReviewedCampaignRuntimeContract : ReviewedCampaignRuntimeContract
canonicalReviewedCampaignRuntimeContract =
  reviewed-campaign-runtime-contract
    campaignDiagnosisExecutable
    campaignExecutable
    reviewManifestFormat
    campaignHopBudget
    true
    true
    true
    true
    true
    true
    false
