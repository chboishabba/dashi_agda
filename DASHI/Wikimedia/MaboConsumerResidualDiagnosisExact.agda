module DASHI.Wikimedia.MaboConsumerResidualDiagnosisExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snow
import DASHI.Core.RobustExperimentInferenceFrontierExact as Experiment
import DASHI.Reasoning.SFMVerifiedClaimPresentation as SFM
import DASHI.Wikimedia.MaboReviewedContextFederationExact as Context
import DASHI.Wikimedia.MaboReviewedEvidencePaymentExact as Payment

------------------------------------------------------------------------
-- MABO CONSUMER-INDEXED RESIDUAL DIAGNOSIS
--
-- This owner does not create a new proof-search, experiment-design,
-- admissibility, WrongType, FactorsThrough or evidence-payment ontology.
-- It binds the existing 100-hop persisted-world surface to one explicit
-- consumer question:
--
--   for each reviewed Mabo context-relation target, is there already a
--   reviewed durable world-identity assignment for that representation?
--
-- A reviewed relation may therefore create an identity-review *demand*.
-- It does not create the identity review or residual payment itself.
------------------------------------------------------------------------

maboContextIdentityConsumer : String
maboContextIdentityConsumer = "consumer:mabo-context-world-identity"

slrExecutable : String
slrExecutable =
  "cargo run -p sensiblaw-world-expansion-runtime --example mabo_100hop_consumer_diagnosis"

requestedHopBudget : Nat
requestedHopBudget = 100

------------------------------------------------------------------------
-- Existing plural-lens discovery routes are reused directly.
------------------------------------------------------------------------

record DiagnosisRouteReceipt : Set where
  constructor diagnosis-route-receipt
  field
    route : Snow.DiscoveryRoute
    routeReference : String
    proposalOnly : Bool
    admissibilityRequired : Bool
    selfCertifiesPayment : Bool
    wrongTypeCanReject : Bool

open DiagnosisRouteReceipt public

proofSearchDiagnosisRoute : DiagnosisRouteReceipt
proofSearchDiagnosisRoute = diagnosis-route-receipt
  Snow.proofSearch
  "repo:proof-search"
  true true false false

failedFactorsThroughDiagnosisRoute : DiagnosisRouteReceipt
failedFactorsThroughDiagnosisRoute = diagnosis-route-receipt
  Snow.failedFactorsThrough
  "DASHI.Core.IntersectionalNonFactorability"
  true true false false

experimentalDesignDiagnosisRoute : DiagnosisRouteReceipt
experimentalDesignDiagnosisRoute = diagnosis-route-receipt
  Snow.experimentalDesign
  "DASHI.Core.RobustExperimentInferenceFrontierExact"
  true true false false

wrongTypeDiagnosisRoute : DiagnosisRouteReceipt
wrongTypeDiagnosisRoute = diagnosis-route-receipt
  Snow.wrongTypeDiagnosis
  "repo:Admissible/FactorsThrough/WrongType"
  true true false true

affectedSubjectDiagnosisRoute : DiagnosisRouteReceipt
affectedSubjectDiagnosisRoute = diagnosis-route-receipt
  Snow.affectedSubjectVoice
  "repo:intersectional-who-is-not-at-the-table"
  true true false false

semiFormalReasoningDiagnosisRoute : DiagnosisRouteReceipt
semiFormalReasoningDiagnosisRoute = diagnosis-route-receipt
  Snow.proofSearch
  "DASHI.Reasoning.SFMVerifiedClaimPresentation"
  true true false false

perplexityArchiveComparisonReference : String
perplexityArchiveComparisonReference =
  "DASHI.Promotion.StandardModelArchiveContextBinding.perplexityOnline"

externalKnowledgeDiagnosisRoute : DiagnosisRouteReceipt
externalKnowledgeDiagnosisRoute = diagnosis-route-receipt
  Snow.externalKnowledgeComparison
  perplexityArchiveComparisonReference
  true true false false

allDiagnosisRoutes : List DiagnosisRouteReceipt
allDiagnosisRoutes =
  proofSearchDiagnosisRoute
  ∷ failedFactorsThroughDiagnosisRoute
  ∷ experimentalDesignDiagnosisRoute
  ∷ wrongTypeDiagnosisRoute
  ∷ affectedSubjectDiagnosisRoute
  ∷ semiFormalReasoningDiagnosisRoute
  ∷ externalKnowledgeDiagnosisRoute
  ∷ []

------------------------------------------------------------------------
-- SFM is an actual donor, not just a prose analogy. Its canonical authority
-- boundary already separates AI generation and diagnostic presentation from
-- verification/theorem promotion, exactly the distinction needed here.
------------------------------------------------------------------------

sfmAIGenerationDoesNotEqualVerification :
  SFM.SFMViewAuthorityBoundary.aiGenerationEqualsVerification
    SFM.canonicalSFMViewAuthorityBoundary ≡ false
sfmAIGenerationDoesNotEqualVerification = refl

sfmDiagnosticPatternDoesNotPromoteTheorem :
  SFM.SFMViewAuthorityBoundary.diagnosticPatternPromotesTheorem
    SFM.canonicalSFMViewAuthorityBoundary ≡ false
sfmDiagnosticPatternDoesNotPromoteTheorem = refl

sfmStatusMustRemainVisible :
  SFM.SFMViewAuthorityBoundary.statusMustRemainVisible
    SFM.canonicalSFMViewAuthorityBoundary ≡ true
sfmStatusMustRemainVisible = refl

------------------------------------------------------------------------
-- Explicit context-world identity consumer.
--
-- These property families are already reviewed bounded Mabo context surfaces.
-- The consumer chooses SameObject as its evidence demand; the property label
-- itself does not infer or pay SameObject.
------------------------------------------------------------------------

record ContextIdentityRequirement : Set where
  constructor context-identity-requirement
  field
    property : Context.MaboContextProperty
    consumerReference : String
    coordinate : Payment.EvidenceCoordinate
    relationReviewPaysCoordinate : Bool

open ContextIdentityRequirement public

participantIdentityRequirement : ContextIdentityRequirement
participantIdentityRequirement = context-identity-requirement
  Context.p710 maboContextIdentityConsumer Payment.sameObject false

jurisdictionIdentityRequirement : ContextIdentityRequirement
jurisdictionIdentityRequirement = context-identity-requirement
  Context.p1001 maboContextIdentityConsumer Payment.sameObject false

courtIdentityRequirement : ContextIdentityRequirement
courtIdentityRequirement = context-identity-requirement
  Context.p4884 maboContextIdentityConsumer Payment.sameObject false

judgeIdentityRequirement : ContextIdentityRequirement
judgeIdentityRequirement = context-identity-requirement
  Context.p1594 maboContextIdentityConsumer Payment.sameObject false

overruledDecisionIdentityRequirement : ContextIdentityRequirement
overruledDecisionIdentityRequirement = context-identity-requirement
  Context.p4006 maboContextIdentityConsumer Payment.sameObject false

contextIdentityRequirements : List ContextIdentityRequirement
contextIdentityRequirements =
  participantIdentityRequirement
  ∷ jurisdictionIdentityRequirement
  ∷ courtIdentityRequirement
  ∷ judgeIdentityRequirement
  ∷ overruledDecisionIdentityRequirement
  ∷ []

------------------------------------------------------------------------
-- Who is not at the table? / missing-carrier theorem.
--
-- Two eligible populations can produce the same realised analytic carrier
-- while differing in whether an eligible member is absent from that carrier.
-- Therefore the missing-population outcome does not factor through the
-- realised carrier. Recharting the realised carrier cannot repair the loss.
------------------------------------------------------------------------

data EligiblePopulationState : Set where
  sameRealisedNoEligibleMissing : EligiblePopulationState
  sameRealisedEligibleMissing : EligiblePopulationState

data RealisedAnalyticCarrier : Set where
  sameRealisedCarrier : RealisedAnalyticCarrier

realisedAnalyticCarrier : EligiblePopulationState → RealisedAnalyticCarrier
realisedAnalyticCarrier sameRealisedNoEligibleMissing = sameRealisedCarrier
realisedAnalyticCarrier sameRealisedEligibleMissing = sameRealisedCarrier

eligibleMemberMissing : EligiblePopulationState → Bool
eligibleMemberMissing sameRealisedNoEligibleMissing = false
eligibleMemberMissing sameRealisedEligibleMissing = true

eligibleMissingOutcomesDiffer :
  eligibleMemberMissing sameRealisedNoEligibleMissing ≡
  eligibleMemberMissing sameRealisedEligibleMissing → ⊥
eligibleMissingOutcomesDiffer ()

eligiblePopulationMissingCarrierWitness :
  INF.NonFactorabilityWitness realisedAnalyticCarrier eligibleMemberMissing
eligiblePopulationMissingCarrierWitness =
  INF.nonFactorabilityWitness
    sameRealisedNoEligibleMissing
    sameRealisedEligibleMissing
    refl
    eligibleMissingOutcomesDiffer

realisedCarrierCannotDetermineEligibleMissingPopulation :
  INF.FactorsThrough realisedAnalyticCarrier eligibleMemberMissing → ⊥
realisedCarrierCannotDetermineEligibleMissingPopulation =
  INF.witnessRulesOutEveryFlatFactorisation
    eligiblePopulationMissingCarrierWitness

------------------------------------------------------------------------
-- Diagnosis/admission boundary.
------------------------------------------------------------------------

record MaboConsumerDiagnosisBoundary : Set where
  constructor mabo-consumer-diagnosis-boundary
  field
    reviewedContextMayProposeIdentityDemand : Bool
    contextReviewPaysIdentityReview : Bool
    arbitraryAdjacencyCreatesConsumerRequirement : Bool
    durableKnownIdentityQuotientedBeforeResidual : Bool
    failedFactorisationMayDemandObserverRepair : Bool
    experimentalDesignMayTargetMissingEvidence : Bool
    experimentDesignCreatesEvidence : Bool
    wrongTypeMayRejectConsumerMismatch : Bool
    externalKnowledgeComparisonMayPropose : Bool
    externalKnowledgeComparisonCreatesPayment : Bool
    semiFormalReasoningMayPresentOpenClaim : Bool
    semiFormalPresentationCreatesPayment : Bool
    candidateOnly : Bool
    createsSemanticAuthority : Bool
    applicabilityPromoted : Bool
    claimTruthPromoted : Bool

open MaboConsumerDiagnosisBoundary public

canonicalDiagnosisBoundary : MaboConsumerDiagnosisBoundary
canonicalDiagnosisBoundary =
  mabo-consumer-diagnosis-boundary
    true
    false
    false
    true
    true
    true
    false
    true
    true
    false
    true
    false
    true
    false
    false
    false

------------------------------------------------------------------------
-- Non-collapse firewalls. Existing Snowball theorems are reused where they
-- already state the exact boundary.
------------------------------------------------------------------------

data ReviewedContextRelationEqualsIdentityReview : Set where
data GraphAdjacencyEqualsConsumerRequirement : Set where
data ExternalKnowledgeComparisonEqualsPayment : Set where
data SemiFormalPresentationEqualsPayment : Set where

contextReviewDoesNotEqualIdentityReview :
  ReviewedContextRelationEqualsIdentityReview → ⊥
contextReviewDoesNotEqualIdentityReview ()

graphAdjacencyDoesNotCreateConsumerRequirement :
  GraphAdjacencyEqualsConsumerRequirement → ⊥
graphAdjacencyDoesNotCreateConsumerRequirement ()

experimentPlanDoesNotCreateEvidence : Snow.ExperimentPlanCreatesEvidence → ⊥
experimentPlanDoesNotCreateEvidence = Snow.experimentPlanDoesNotCreateEvidence

wrongTypeAdjacencyDoesNotCreateIdentity : Snow.WrongTypeAdjacencyCreatesTypeIdentity → ⊥
wrongTypeAdjacencyDoesNotCreateIdentity = Snow.wrongTypeAdjacencyDoesNotCreateIdentity

externalKnowledgeComparisonDoesNotCreatePayment :
  ExternalKnowledgeComparisonEqualsPayment → ⊥
externalKnowledgeComparisonDoesNotCreatePayment ()

semiFormalPresentationDoesNotCreatePayment :
  SemiFormalPresentationEqualsPayment → ⊥
semiFormalPresentationDoesNotCreatePayment ()

------------------------------------------------------------------------
-- This tranche is a source contract for the runtime executable above.
-- It deliberately records no execution/kernel success bit.
------------------------------------------------------------------------

record RuntimeContract : Set where
  constructor runtime-contract
  field
    executableReference : String
    maxHopBudget : Nat
    durableIdentityBaselineRequired : Bool
    reviewedContextProvenanceRequired : Bool
    emitsOpenSameObjectResiduals : Bool
    autoReviewsIdentity : Bool

open RuntimeContract public

canonicalRuntimeContract : RuntimeContract
canonicalRuntimeContract = runtime-contract
  slrExecutable
  requestedHopBudget
  true
  true
  true
  false
