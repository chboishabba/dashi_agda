module DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact where

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F
--
-- O. Objective.
-- Connect existing SensibLaw, matter-workflow, compliance, and governance
-- non-promotion proofs to the focused DASHI TOE graph.
--
-- R. Reuse.
-- Reuse the existing operational/semantic boundary, live review mutation,
-- matter acceptance, provenance/status orthogonality, source-realised legal
-- rule, source-conditioned applicability, compliance composition, governance
-- control case, and formalisation-governance capstone.
--
-- C. Construction.
-- Expose one normalized theorem surface.
-- Expose the existing compliance composition handoff.
-- Add no new workflow, legal-rule, compliance, or authority semantics.
--
-- S. Safety invariants.
-- Operational completion is not world truth.
-- Database commit is not semantic authority.
-- Accepted review status does not pay legal applicability.
-- Matter acceptance is not claim truth.
-- Source attribution is not claim truth.
-- Legal authority is not claim truth.
-- Citation alone does not realise a legal rule.
-- A semantic meet alone does not prove legal applicability.
-- A source-realised wrong type does not automatically prove violation.
-- Control evidence does not create truth.
-- A passing control does not create certification.
-- Kernel closure does not create semantic closure.
--
-- L. Lane.
-- This module owns only TOE normalization.
-- It does not edit ESD or digital_esd surfaces.
-- It does not create an Actionstep-specific ontology.
-- Actionstep-style task and matter workflow state is represented by the
-- existing generic operational, review, and matter owners.
--
-- P. Postconditions.
-- TOE consumers reach one exact governance non-promotion surface.
-- Original theorem owners retain proof ownership.
-- Unifier may expose aliases but does not supply proof authority.
--
-- G. Governance.
-- Existing ITIR governance controls remain the standards-mapping owner.
-- Standards references are design lenses only.
-- No standards certification is claimed.
--
-- F. Verification.
-- Source read-back must resolve every owner and alias below.
-- Exact-head kernel certification remains a separate receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CompositionalComplianceExact as Compliance
import DASHI.Core.ITIRGovernanceControlCaseExact as Control
import DASHI.Governance.FormalisationGovernanceCapstoneExact as Formalisation
import DASHI.Cognition.PNF.SensibLawOperationalSemanticBoundaryExact as Operational
import DASHI.Cognition.PNF.SensibLawLiveReviewMutationExact as Review
import DASHI.Cognition.PNF.SensibLawMatterAcceptanceExact as Matter
import DASHI.Cognition.PNF.SensibLawProvenanceSemanticStatusOrthogonalityExact as Status
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawSourceConditionedApplicabilityViolationExact as Applicability
import DASHI.Interop.ITIRFederatedTypedWorldProjectionExact as Suite
import DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact as Fabric
import DASHI.Security.AgentAuthorityTrajectoryExact as Authority
import DASHI.Interop.SLRReviewPromoteAbstainConsumerExact as PromotionReview
import DASHI.Interop.SLRRuntimeValidationHandoffExact as RuntimeValidation
import DASHI.Interop.SLRValidationRoadmapPromotionExact as ValidationRoadmap
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission
import DASHI.Cognition.PNF.SensibLawSemanticExpansionSoftwareValidationExact as SoftwareValidation

------------------------------------------------------------------------
-- Type aliases keep Unifier thin.
------------------------------------------------------------------------

TaskCompletionCreatesTruth : Set
TaskCompletionCreatesTruth = Operational.TaskCompletionCreatesTruth

ReviewActivityCreatesAdmission : Set
ReviewActivityCreatesAdmission = Operational.ReviewActivityCreatesAdmission

DatabaseCommitCreatesSemanticAuthority : Set
DatabaseCommitCreatesSemanticAuthority =
  Review.DatabaseCommitCreatesSemanticAuthority

DurableReviewStateCreatesTruth : Set
DurableReviewStateCreatesTruth = Review.DurableReviewStateCreatesTruth

AcceptedStatusPaysApplicability : Set
AcceptedStatusPaysApplicability = Review.AcceptedStatusPaysApplicability

AcceptanceRoleCreatesTruth : Set
AcceptanceRoleCreatesTruth = Matter.AcceptanceRoleCreatesTruth

AcceptanceReceiptMutatesMatter : Set
AcceptanceReceiptMutatesMatter = Matter.AcceptanceReceiptMutatesMatter

ExternalSourceClaimImpliesTruthAdmitted : Set
ExternalSourceClaimImpliesTruthAdmitted =
  Status.ExternalSourceClaimImpliesTruthAdmitted

LegalAuthorityCreatesTruthStatus : Set
LegalAuthorityCreatesTruthStatus = Status.LegalAuthorityCreatesTruthStatus

PromotionStageMaySkipPromotionAuthority : Set
PromotionStageMaySkipPromotionAuthority =
  Status.PromotionStageMaySkipPromotionAuthority

CitationAloneRealisesLegalRule : Set
CitationAloneRealisesLegalRule = SourceRule.CitationAloneRealisesLegalRule

SemanticMeetAloneProvesLegalApplicability : Set
SemanticMeetAloneProvesLegalApplicability =
  Applicability.SemanticMeetAloneProvesLegalApplicability

SourceRealisedWrongTypeAutomaticallyViolated : Set
SourceRealisedWrongTypeAutomaticallyViolated =
  Applicability.SourceRealisedWrongTypeAutomaticallyViolated

AllElementsProvedIgnoresExceptionsDefences : Set
AllElementsProvedIgnoresExceptionsDefences =
  Applicability.AllElementsProvedIgnoresExceptionsDefences

ControlEvidenceCreatesTruth : Set
ControlEvidenceCreatesTruth = Control.ControlEvidenceCreatesTruth

PassingControlMeansCertified : Set
PassingControlMeansCertified = Control.PassingControlMeansCertified

------------------------------------------------------------------------
-- Exact theorem aliases.
------------------------------------------------------------------------

toeTaskCompletionDoesNotCreateTruth :
  TaskCompletionCreatesTruth → ⊥
toeTaskCompletionDoesNotCreateTruth =
  Operational.taskCompletionDoesNotCreateTruth

toeReviewActivityNeedsSeparateAdmissionReceipt :
  ReviewActivityCreatesAdmission → ⊥
toeReviewActivityNeedsSeparateAdmissionReceipt =
  Operational.reviewActivityNeedsSeparateAdmissionReceipt

toeDatabaseCommitDoesNotCreateSemanticAuthority :
  DatabaseCommitCreatesSemanticAuthority → ⊥
toeDatabaseCommitDoesNotCreateSemanticAuthority =
  Review.databaseCommitDoesNotCreateSemanticAuthority

toeDurableReviewStateDoesNotCreateTruth :
  DurableReviewStateCreatesTruth → ⊥
toeDurableReviewStateDoesNotCreateTruth =
  Review.durableReviewStateDoesNotCreateTruth

toeAcceptedReviewDoesNotPayApplicability :
  AcceptedStatusPaysApplicability → ⊥
toeAcceptedReviewDoesNotPayApplicability =
  Review.acceptedStatusDoesNotPayApplicability

toeMatterAcceptanceDoesNotCreateTruth :
  AcceptanceRoleCreatesTruth → ⊥
toeMatterAcceptanceDoesNotCreateTruth =
  Matter.acceptanceRoleDoesNotCreateTruth

toeAcceptanceReceiptDoesNotMutateMatter :
  AcceptanceReceiptMutatesMatter → ⊥
toeAcceptanceReceiptDoesNotMutateMatter =
  Matter.acceptanceReceiptDoesNotMutateMatter

toeExternalSourceDoesNotAdmitTruth :
  ExternalSourceClaimImpliesTruthAdmitted → ⊥
toeExternalSourceDoesNotAdmitTruth =
  Status.externalSourceDoesNotAdmitTruth

toeLegalAuthorityDoesNotCreateTruthStatus :
  LegalAuthorityCreatesTruthStatus → ⊥
toeLegalAuthorityDoesNotCreateTruthStatus =
  Status.legalAuthorityDoesNotCreateTruthStatus

toePromotionStageDoesNotBypassPromotionAuthority :
  PromotionStageMaySkipPromotionAuthority → ⊥
toePromotionStageDoesNotBypassPromotionAuthority =
  Status.promotionStageDoesNotBypassPromotionAuthority

toeCitationAloneDoesNotRealiseLegalRule :
  CitationAloneRealisesLegalRule → ⊥
toeCitationAloneDoesNotRealiseLegalRule =
  SourceRule.citationAloneDoesNotRealiseLegalRule

toeSemanticMeetDoesNotProveLegalApplicability :
  SemanticMeetAloneProvesLegalApplicability → ⊥
toeSemanticMeetDoesNotProveLegalApplicability =
  Applicability.semanticMeetDoesNotAloneProveLegalApplicability

toeSourceRealisedWrongTypeDoesNotAutoViolate :
  SourceRealisedWrongTypeAutomaticallyViolated → ⊥
toeSourceRealisedWrongTypeDoesNotAutoViolate =
  Applicability.sourceRealisedWrongTypeDoesNotAutoViolate

toeElementsDoNotEraseExceptionsOrDefences :
  AllElementsProvedIgnoresExceptionsDefences → ⊥
toeElementsDoNotEraseExceptionsOrDefences =
  Applicability.allElementsDoNotEraseExceptionsDefences

toeControlEvidenceDoesNotCreateTruth :
  ControlEvidenceCreatesTruth → ⊥
toeControlEvidenceDoesNotCreateTruth =
  Control.controlEvidenceDoesNotCreateTruth

toePassingControlDoesNotMeanCertified :
  PassingControlMeansCertified → ⊥
toePassingControlDoesNotMeanCertified =
  Control.passingDoesNotMeanCertified

toeKernelClosureDoesNotMeanSemanticClosure :
  Formalisation.ThreeStoreyBoundary.kernelClosureEqualsSemanticClosure
    Formalisation.canonicalThreeStoreyBoundary
  ≡ false
toeKernelClosureDoesNotMeanSemanticClosure =
  Formalisation.ThreeStoreyBoundary.kernelClosureEqualsSemanticClosureIsFalse
    Formalisation.canonicalThreeStoreyBoundary

------------------------------------------------------------------------
-- Existing proof-carrying compliance handoff.
------------------------------------------------------------------------

TOECertifiedStage :
  (Input Output : Set) →
  (Input → Output → Set) →
  Set₁
TOECertifiedStage = Compliance.CertifiedStage

TOECompositeCompliance :
  ∀ {A B C : Set} →
  (A → B → Set) →
  (B → C → Set) →
  A →
  C →
  Set
TOECompositeCompliance = Compliance.CompositeCompliance

toeComposeCertifiedStages :
  ∀ {A B C : Set}
    {First : A → B → Set}
    {Second : B → C → Set}
    (left : Compliance.CertifiedStage A B First)
    (right : Compliance.CertifiedStage B C Second) →
  Compliance.input right ≡ Compliance.output left →
  Compliance.CompositeCompliance
    First
    Second
    (Compliance.input left)
    (Compliance.output right)
toeComposeCertifiedStages =
  Compliance.composeCertifiedStages

------------------------------------------------------------------------
-- Promotion, validation, and admission non-promotion handoff.
--
-- Reuse exact owners.
-- Review eligibility is not promotion.
-- Runtime parity is not world truth.
-- Implementation is not runtime certification.
-- Parser output is not admission authority.
-- Software validation is not publication authority.
------------------------------------------------------------------------

ReviewEligibilityCreatesPromotionReceipt : Set
ReviewEligibilityCreatesPromotionReceipt =
  PromotionReview.ReviewEligibilityCreatesPromotionReceipt

EligibilityMeansTruth : Set
EligibilityMeansTruth =
  PromotionReview.EligibilityMeansTruth

ZeroParityFailuresMeansWorldTruth : Set
ZeroParityFailuresMeansWorldTruth =
  RuntimeValidation.ZeroParityFailuresMeansWorldTruth

DiagnosticLegalStreamMeansLegalCertification : Set
DiagnosticLegalStreamMeansLegalCertification =
  RuntimeValidation.DiagnosticLegalStreamMeansLegalCertification

CanonicalClaimProjectionPaysClaimTruth : Set
CanonicalClaimProjectionPaysClaimTruth =
  ValidationRoadmap.CanonicalClaimProjectionPaysClaimTruth

ReviewRouterImplementationPaysConsumerAdequacy : Set
ReviewRouterImplementationPaysConsumerAdequacy =
  ValidationRoadmap.ReviewRouterImplementationPaysConsumerAdequacy

ParserCandidateAloneAuthorizesAdmission : Set
ParserCandidateAloneAuthorizesAdmission =
  Admission.ParserCandidateAloneAuthorizesAdmission

ResidualPriorityScoreIsTruthConfidence : Set
ResidualPriorityScoreIsTruthConfidence =
  Admission.ResidualPriorityScoreIsTruthConfidence

AdmissionReceiptPublishesGeneration : Set
AdmissionReceiptPublishesGeneration =
  Admission.AdmissionReceiptPublishesGeneration

SoftwareValidationAuthorizesPublication : Set
SoftwareValidationAuthorizesPublication =
  SoftwareValidation.SoftwareValidationAuthorizesPublication

LaterValidatedHeadRetroactivelyChangesCertifiedBaseline : Set
LaterValidatedHeadRetroactivelyChangesCertifiedBaseline =
  SoftwareValidation.LaterValidatedHeadRetroactivelyChangesCertifiedBaseline

toeReviewEligibilityDoesNotCreatePromotion :
  ReviewEligibilityCreatesPromotionReceipt → ⊥
toeReviewEligibilityDoesNotCreatePromotion =
  PromotionReview.eligibilityCannotManufacturePromotion

toeReviewEligibilityDoesNotCreateTruth :
  EligibilityMeansTruth → ⊥
toeReviewEligibilityDoesNotCreateTruth =
  PromotionReview.eligibilityDoesNotMeanTruth

toeRuntimeParityDoesNotCreateWorldTruth :
  ZeroParityFailuresMeansWorldTruth → ⊥
toeRuntimeParityDoesNotCreateWorldTruth =
  RuntimeValidation.zeroParityFailuresDoNotMeanWorldTruth

toeDiagnosticStreamDoesNotCreateLegalCertification :
  DiagnosticLegalStreamMeansLegalCertification → ⊥
toeDiagnosticStreamDoesNotCreateLegalCertification =
  RuntimeValidation.diagnosticStreamDoesNotMeanLegalCertification

toeProjectionDoesNotCreateClaimTruth :
  CanonicalClaimProjectionPaysClaimTruth → ⊥
toeProjectionDoesNotCreateClaimTruth =
  ValidationRoadmap.projectionDoesNotPayClaimTruth

toeReviewRouterDoesNotCreateConsumerAdequacy :
  ReviewRouterImplementationPaysConsumerAdequacy → ⊥
toeReviewRouterDoesNotCreateConsumerAdequacy =
  ValidationRoadmap.routerDoesNotPayAdequacy

toeParserCandidateDoesNotAuthorizeAdmission :
  ParserCandidateAloneAuthorizesAdmission → ⊥
toeParserCandidateDoesNotAuthorizeAdmission =
  Admission.parserCandidateAloneCannotAuthorizeAdmission

toeResidualPriorityDoesNotCreateTruthConfidence :
  ResidualPriorityScoreIsTruthConfidence → ⊥
toeResidualPriorityDoesNotCreateTruthConfidence =
  Admission.residualPriorityIsNotTruthConfidence

toeAdmissionReceiptDoesNotPublishGeneration :
  AdmissionReceiptPublishesGeneration → ⊥
toeAdmissionReceiptDoesNotPublishGeneration =
  Admission.admissionReceiptDoesNotPublishGeneration

toeSoftwareValidationDoesNotAuthorizePublication :
  SoftwareValidationAuthorizesPublication → ⊥
toeSoftwareValidationDoesNotAuthorizePublication =
  SoftwareValidation.softwareValidationDoesNotAuthorizePublication

toeLaterValidationDoesNotRewriteCertifiedBaseline :
  LaterValidatedHeadRetroactivelyChangesCertifiedBaseline → ⊥
toeLaterValidationDoesNotRewriteCertifiedBaseline =
  SoftwareValidation.laterValidationDoesNotRewriteCertifiedBaseline

toeRuntimeReviewContract : PromotionReview.RuntimeReviewContract
toeRuntimeReviewContract =
  PromotionReview.canonicalRuntimeReviewContract

toeRuntimeValidationBoundary : RuntimeValidation.SLRValidationBoundary
toeRuntimeValidationBoundary =
  RuntimeValidation.canonicalSLRValidationBoundary

toeValidationPromotionBoundary :
  ValidationRoadmap.ValidationPromotionBoundary
toeValidationPromotionBoundary =
  ValidationRoadmap.canonicalValidationPromotionBoundary

toeLegalSemanticAdmissionFrontier :
  Admission.LegalSemanticAdmissionFrontier
toeLegalSemanticAdmissionFrontier =
  Admission.currentLegalSemanticAdmissionFrontier

toeSemanticExpansionValidationReceipt :
  SoftwareValidation.SemanticExpansionSoftwareValidationReceipt
toeSemanticExpansionValidationReceipt =
  SoftwareValidation.semanticExpansionSoftwareValidation

record GovernedLegalWorkflowPromotionBoundary : Set where
  constructor governed-legal-workflow-promotion-boundary
  field
    reviewEligibilityCreatesPromotion : Bool
    reviewEligibilityCreatesPromotionIsFalse :
      reviewEligibilityCreatesPromotion ≡ false

    runtimeParityCreatesWorldTruth : Bool
    runtimeParityCreatesWorldTruthIsFalse :
      runtimeParityCreatesWorldTruth ≡ false

    diagnosticStreamCreatesLegalCertification : Bool
    diagnosticStreamCreatesLegalCertificationIsFalse :
      diagnosticStreamCreatesLegalCertification ≡ false

    claimProjectionCreatesTruth : Bool
    claimProjectionCreatesTruthIsFalse :
      claimProjectionCreatesTruth ≡ false

    reviewRouterCreatesConsumerAdequacy : Bool
    reviewRouterCreatesConsumerAdequacyIsFalse :
      reviewRouterCreatesConsumerAdequacy ≡ false

    parserCandidateCreatesAdmissionAuthority : Bool
    parserCandidateCreatesAdmissionAuthorityIsFalse :
      parserCandidateCreatesAdmissionAuthority ≡ false

    residualPriorityCreatesTruthConfidence : Bool
    residualPriorityCreatesTruthConfidenceIsFalse :
      residualPriorityCreatesTruthConfidence ≡ false

    admissionReceiptCreatesPublicationAuthority : Bool
    admissionReceiptCreatesPublicationAuthorityIsFalse :
      admissionReceiptCreatesPublicationAuthority ≡ false

    softwareValidationCreatesPublicationAuthority : Bool
    softwareValidationCreatesPublicationAuthorityIsFalse :
      softwareValidationCreatesPublicationAuthority ≡ false

    laterValidationRewritesCertifiedBaseline : Bool
    laterValidationRewritesCertifiedBaselineIsFalse :
      laterValidationRewritesCertifiedBaseline ≡ false

open GovernedLegalWorkflowPromotionBoundary public

canonicalGovernedLegalWorkflowPromotionBoundary :
  GovernedLegalWorkflowPromotionBoundary
canonicalGovernedLegalWorkflowPromotionBoundary =
  governed-legal-workflow-promotion-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl


------------------------------------------------------------------------
-- Normalized TOE boundary.
------------------------------------------------------------------------

record GovernedLegalWorkflowTOEBoundary : Set where
  constructor governed-legal-workflow-toe-boundary
  field
    operationalCompletionCreatesTruth : Bool
    operationalCompletionCreatesTruthIsFalse :
      operationalCompletionCreatesTruth ≡ false

    databaseCommitCreatesSemanticAuthority : Bool
    databaseCommitCreatesSemanticAuthorityIsFalse :
      databaseCommitCreatesSemanticAuthority ≡ false

    acceptedReviewPaysApplicability : Bool
    acceptedReviewPaysApplicabilityIsFalse :
      acceptedReviewPaysApplicability ≡ false

    matterAcceptanceCreatesTruth : Bool
    matterAcceptanceCreatesTruthIsFalse :
      matterAcceptanceCreatesTruth ≡ false

    sourceAttributionCreatesTruth : Bool
    sourceAttributionCreatesTruthIsFalse :
      sourceAttributionCreatesTruth ≡ false

    legalAuthorityCreatesTruth : Bool
    legalAuthorityCreatesTruthIsFalse :
      legalAuthorityCreatesTruth ≡ false

    citationAloneRealisesLegalRule : Bool
    citationAloneRealisesLegalRuleIsFalse :
      citationAloneRealisesLegalRule ≡ false

    semanticMeetAloneProvesApplicability : Bool
    semanticMeetAloneProvesApplicabilityIsFalse :
      semanticMeetAloneProvesApplicability ≡ false

    sourceRealisedWrongTypeAutomaticallyViolates : Bool
    sourceRealisedWrongTypeAutomaticallyViolatesIsFalse :
      sourceRealisedWrongTypeAutomaticallyViolates ≡ false

    controlEvidenceCreatesTruth : Bool
    controlEvidenceCreatesTruthIsFalse :
      controlEvidenceCreatesTruth ≡ false

    passingControlMeansCertification : Bool
    passingControlMeansCertificationIsFalse :
      passingControlMeansCertification ≡ false

    kernelClosureMeansSemanticClosure : Bool
    kernelClosureMeansSemanticClosureIsFalse :
      kernelClosureMeansSemanticClosure ≡ false

    complianceCompositionRetainsIntermediateWitness : Bool
    complianceCompositionRetainsIntermediateWitnessIsTrue :
      complianceCompositionRetainsIntermediateWitness ≡ true

open GovernedLegalWorkflowTOEBoundary public

canonicalGovernedLegalWorkflowTOEBoundary :
  GovernedLegalWorkflowTOEBoundary
canonicalGovernedLegalWorkflowTOEBoundary =
  governed-legal-workflow-toe-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl


------------------------------------------------------------------------
-- Cross-suite authority handoff.
--
-- Reuse existing owners.
-- Do not infer new authority from workflow state.
------------------------------------------------------------------------

CaseySelectionCreatesWorldTruth : Set
CaseySelectionCreatesWorldTruth =
  Suite.CaseySelectionCreatesWorldTruth

KnowledgeIsAuthority : Set
KnowledgeIsAuthority =
  Authority.KnowledgeIsAuthority

toeSuiteRoleMap : Suite.SuiteRoleMap
toeSuiteRoleMap = Suite.canonicalSuiteRoleMap

toeCaseySelectionDoesNotCreateWorldTruth :
  CaseySelectionCreatesWorldTruth → ⊥
toeCaseySelectionDoesNotCreateWorldTruth =
  Suite.caseySelectionIsNotWorldTruth

toeFormalProofDoesNotCreateExternalWorldTruth :
  Suite.FormalProofCreatesExternalWorldTruth → ⊥
toeFormalProofDoesNotCreateExternalWorldTruth =
  Suite.formalProofIsNotExternalWorldTruth

toeKnowledgeDoesNotCreateExecutionAuthority :
  KnowledgeIsAuthority → ⊥
toeKnowledgeDoesNotCreateExecutionAuthority =
  Authority.knowledgeIsNotAuthority

toeMetaIntrospectorContribution : Fabric.ContributionAttribution
toeMetaIntrospectorContribution =
  Fabric.jmdRepositoryContribution

toeMetaIntrospectorAttributionRule : String
toeMetaIntrospectorAttributionRule =
  Fabric.attributionRule

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F control receipt.
--
-- This record is process metadata.
-- It adds no legal rule.
-- It adds no semantic authority.
-- It adds no standards certification.
------------------------------------------------------------------------

record GovernedLegalWorkflowZKPReceipt : Set where
  constructor governed-legal-workflow-zkp-receipt
  field
    objectiveRefs : List String
    reuseRefs : List String
    constructionRefs : List String
    safetyInvariantRefs : List String
    laneRefs : List String
    preconditionRefs : List String
    postconditionRefs : List String
    governanceRefs : List String
    verificationRefs : List String

    standardsAreDesignLenses : Bool
    standardsAreDesignLensesIsTrue :
      standardsAreDesignLenses ≡ true

    standardsCertificationClaimed : Bool
    standardsCertificationClaimedIsFalse :
      standardsCertificationClaimed ≡ false

    esdSurfaceMutationAllowed : Bool
    esdSurfaceMutationAllowedIsFalse :
      esdSurfaceMutationAllowed ≡ false

    metaIntrospectorRepositoriesOwnDASHITheorems : Bool
    metaIntrospectorRepositoriesOwnDASHITheoremsIsFalse :
      metaIntrospectorRepositoriesOwnDASHITheorems ≡ false

open GovernedLegalWorkflowZKPReceipt public

canonicalGovernedLegalWorkflowZKPReceipt :
  GovernedLegalWorkflowZKPReceipt
canonicalGovernedLegalWorkflowZKPReceipt =
  governed-legal-workflow-zkp-receipt
    ( "Converge exact SensibLaw and legal-workflow governance proofs into the focused DASHI TOE import graph."
    ∷ [] )
    ( "DASHI.Core.CompositionalComplianceExact"
    ∷ "DASHI.Core.ITIRGovernanceControlCaseExact"
    ∷ "DASHI.Governance.FormalisationGovernanceCapstoneExact"
    ∷ "DASHI.Cognition.PNF.SensibLawOperationalSemanticBoundaryExact"
    ∷ "DASHI.Cognition.PNF.SensibLawLiveReviewMutationExact"
    ∷ "DASHI.Cognition.PNF.SensibLawMatterAcceptanceExact"
    ∷ "DASHI.Cognition.PNF.SensibLawProvenanceSemanticStatusOrthogonalityExact"
    ∷ "DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact"
    ∷ "DASHI.Cognition.PNF.SensibLawSourceConditionedApplicabilityViolationExact"
    ∷ "DASHI.Interop.ITIRFederatedTypedWorldProjectionExact"
    ∷ "DASHI.Security.AgentAuthorityTrajectoryExact"
    ∷ "DASHI.Interop.SLRReviewPromoteAbstainConsumerExact"
    ∷ "DASHI.Interop.SLRRuntimeValidationHandoffExact"
    ∷ "DASHI.Interop.SLRValidationRoadmapPromotionExact"
    ∷ "DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact"
    ∷ "DASHI.Cognition.PNF.SensibLawSemanticExpansionSoftwareValidationExact"
    ∷ [] )
    ( "Normalize exact theorem aliases only."
    ∷ "Retain the intermediate compliance witness."
    ∷ "Expose the existing cross-suite role map."
    ∷ [] )
    ( "Task completion does not create truth."
    ∷ "Database commit does not create semantic authority."
    ∷ "Accepted review does not pay legal applicability."
    ∷ "Matter acceptance does not create truth."
    ∷ "Citation does not realise a legal rule by itself."
    ∷ "A semantic meet does not prove legal applicability by itself."
    ∷ "Control evidence does not create truth."
    ∷ "A passing control does not create certification."
    ∷ "Casey selection does not create world truth."
    ∷ "Knowledge does not create execution authority."
    ∷ "Kernel closure does not create semantic closure."
    ∷ "Review eligibility does not create promotion or truth."
    ∷ "Runtime parity does not create world truth."
    ∷ "A diagnostic legal stream does not create legal certification."
    ∷ "Claim projection does not create claim truth."
    ∷ "A review router does not create consumer adequacy."
    ∷ "A parser candidate does not authorize admission."
    ∷ "Residual priority does not create truth confidence."
    ∷ "An admission receipt does not authorize publication."
    ∷ "Software validation does not authorize publication."
    ∷ "Later validation does not rewrite the certified baseline."
    ∷ [] )
    ( "dashi_agda is the formal reference lane."
    ∷ "SensibLaw/SLR owns review, admission, semantic construction, and legal consumer projection."
    ∷ "casey-git-clone owns candidate, workspace, selection, collapse, and build authority."
    ∷ "Meta-introspector repositories remain process and implementation context only."
    ∷ "ESD surfaces are import-only for this TOE lane."
    ∷ [] )
    ( "Every imported proof owner exists."
    ∷ "The focused TOE root imports the normalized bridge."
    ∷ "DASHI.Unifier exposes aliases only."
    ∷ "No ESD or digital_esd path is edited."
    ∷ "No trust escape is introduced."
    ∷ [] )
    ( "The TOE root reaches the exact governance non-promotion proofs."
    ∷ "The TOE root reaches the cross-suite authority firewalls."
    ∷ "Original theorem owners keep proof ownership."
    ∷ "Meta-introspector repositories keep source attribution."
    ∷ "Standards remain control lenses only."
    ∷ "The TOE root reaches review-to-promotion non-promotion proofs."
    ∷ "The TOE root reaches runtime-validation and roadmap-promotion firewalls."
    ∷ "The TOE root reaches legal semantic admission and software-validation firewalls."
    ∷ [] )
    ( "ITIL change and service-management lens."
    ∷ "ISO 9000 family quality-management lens."
    ∷ "ISO/IEC 42001 AI-management lens."
    ∷ "ISO/IEC 27001 information-security lens."
    ∷ "ISO/IEC 27701 privacy-information lens."
    ∷ "ISO/IEC 23894 AI-risk lens."
    ∷ "ISO 9241 human-system interaction lens."
    ∷ "NIST AI RMF Govern, Map, Measure, and Manage lens."
    ∷ "Six Sigma DMAIC quality-control lens."
    ∷ "C4 and PlantUML architecture-view lens."
    ∷ "ASD-STE100 plain-language writing lens."
    ∷ [] )
    ( "Run dashi-repo related for reused theorem owners."
    ∷ "Run dashi-repo discover for the governance handoff."
    ∷ "Run dashi-repo lineage for SensibLaw and Unified owners."
    ∷ "Run the focused static contract."
    ∷ "Run dashi-agda-preflight on the bridge, regression, TOE root, and Unifier."
    ∷ "Reject trust escapes."
    ∷ "Reject ESD path changes."
    ∷ "Kernel-check the focused Agda path."
    ∷ "Resolve review, validation, promotion, admission, and software-validation owners with repository intelligence."
    ∷ [] )
    true refl
    false refl
    false refl
    false refl

toeProcessContextRefs : List String
toeProcessContextRefs =
  "meta-introspector/zkperf — process and tooling context; no theorem copied"
  ∷ "meta-introspector/zos-server — reconciliation/runtime context; original attribution retained"
  ∷ "meta-introspector/erdfa-py — process/tooling context; original attribution retained"
  ∷ "meta-introspector/aristotle-cli-rs — proof-project tooling context; original attribution retained"
  ∷ "chboishabba/zkSEC — authority/receipt process context; no theorem copied"
  ∷ []
