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
import DASHI.Core.BoundAcquisitionDemandExact as BoundAcquisition
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNonPromotion
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
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as LegalAuthority
import DASHI.Cognition.PNF.SensibLawSemanticExpansionSoftwareValidationExact as SoftwareValidation
import DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerExact as DbNative
import DASHI.Interop.SensibLawSemanticPromotionPolicy as SemanticPromotion
import DASHI.Interop.IntrospectiveProofLoopExact as Introspection
import DASHI.Law.SensibLawNativeLegalFollowCLIExact as NativeLegalFollow
import DASHI.Law.SensibLawPreferredAustralianAuthorityAcquisitionExact as ProviderAcquisition
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as ExpertProduction
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as RealMatterReview
import DASHI.Governance.LegalDecisionDoubleProjectionExact as LegalDecision
import DASHI.Governance.LegitimacyEvidenceSeparationExact as Legitimacy
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain
import DASHI.Governance.PromotionSpine as Promotion
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.GovernedArtifactCore as Governed

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

LegalReviewDecisionCreatesClaimTruth : Set
LegalReviewDecisionCreatesClaimTruth =
  RealMatterReview.LegalReviewDecisionCreatesClaimTruth

OfficialLegalSurfaceRecoversFineState : Set
OfficialLegalSurfaceRecoversFineState =
  NF.FactorsThrough
    LegalDecision.officialSurface
    LegalDecision.fineLegalStateOf

LegalOnlyCreatesLegitimacy : Set₁
LegalOnlyCreatesLegitimacy =
  Legitimacy.AdmittedLegitimacy
    Legitimacy.demoEvidence
    Legitimacy.legalOnly

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
-- Canonical semantic-authority and bound-acquisition non-promotion.
--
-- Reuse the existing owners.
-- Semantic evidence classification creates no truth or legal authority.
-- Binding work to an exact residual and producer still does not pay the
-- requirement or close the consumer.
------------------------------------------------------------------------

BoundDemandAutomaticallyPaysRequirement : Set
BoundDemandAutomaticallyPaysRequirement =
  BoundAcquisition.BoundDemandAutomaticallyPaysRequirement

BoundDemandAutomaticallyClosesConsumer : Set
BoundDemandAutomaticallyClosesConsumer =
  BoundAcquisition.BoundDemandAutomaticallyClosesConsumer

SameProducerIdentifiesResidual : Set
SameProducerIdentifiesResidual =
  BoundAcquisition.SameProducerIdentifiesResidual

SemanticPromotionTruthAuthorityClosed : Set
SemanticPromotionTruthAuthorityClosed =
  AuthorityNonPromotion.truthAuthorityFlag
    SemanticPromotion.semanticPromotionAuthorityBoundary
  ≡ false

SemanticPromotionLegalAuthorityClosed : Set
SemanticPromotionLegalAuthorityClosed =
  AuthorityNonPromotion.legalAuthorityFlag
    SemanticPromotion.semanticPromotionAuthorityBoundary
  ≡ false

SemanticPromotionAllAuthorityClosed : Set
SemanticPromotionAllAuthorityClosed =
  AuthorityNonPromotion.promotesAnyAuthority
    SemanticPromotion.semanticPromotionAuthorityBoundary
  ≡ false

toeSemanticPromotionTruthAuthorityClosed :
  SemanticPromotionTruthAuthorityClosed
toeSemanticPromotionTruthAuthorityClosed =
  SemanticPromotion.semantic-promotion-truth-authority-closed

toeSemanticPromotionLegalAuthorityClosed :
  SemanticPromotionLegalAuthorityClosed
toeSemanticPromotionLegalAuthorityClosed =
  SemanticPromotion.semantic-promotion-legal-authority-closed

toeSemanticPromotionAllAuthorityClosed :
  SemanticPromotionAllAuthorityClosed
toeSemanticPromotionAllAuthorityClosed =
  SemanticPromotion.semantic-promotion-all-authority-closed

toeBoundAcquisitionDoesNotPayRequirement :
  BoundDemandAutomaticallyPaysRequirement → ⊥
toeBoundAcquisitionDoesNotPayRequirement =
  BoundAcquisition.bindingDoesNotPayRequirement

toeBoundAcquisitionDoesNotCloseConsumer :
  BoundDemandAutomaticallyClosesConsumer → ⊥
toeBoundAcquisitionDoesNotCloseConsumer =
  BoundAcquisition.bindingDoesNotCloseConsumer

toeProducerIdentityDoesNotIdentifyResidual :
  SameProducerIdentifiesResidual → ⊥
toeProducerIdentityDoesNotIdentifyResidual =
  BoundAcquisition.producerIdentityDoesNotIdentifyResidual

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
-- Canonical generic ZKP frame.
--
-- Reuse the existing IntrospectiveProofLoopExact ZKPFrame.
-- The legal-workflow receipt below remains the detailed control ledger.
-- This value binds that ledger to the repository-wide O/R/C/S/L/P/G/F frame.
------------------------------------------------------------------------

GovernedLegalWorkflowIntrospectiveZKPFrame : Set
GovernedLegalWorkflowIntrospectiveZKPFrame =
  Introspection.ZKPFrame

canonicalGovernedLegalWorkflowIntrospectiveZKPFrame :
  GovernedLegalWorkflowIntrospectiveZKPFrame
canonicalGovernedLegalWorkflowIntrospectiveZKPFrame =
  Introspection.zkp-frame
    "dashi_agda focused DASHI TOE legal-governance lane"
    "Converge SensibLaw and Actionstep-style legal workflow governance into existing TOE owners."
    "DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact"
    "canonicalGovernedLegalWorkflowTOEInvariantHandoff"
    "SensibLaw residual, review, admission, compliance, and authority non-promotion surfaces"
    "Reuse exact owners; expose one bridge through Unified.Everything, Unifier, and EverythingTOESymmetryResolved369."
    "One canonical governed legal-workflow handoff with fail-closed semantic and authority promotion."
    "Jurisdiction-specific evidence, exact-head kernel receipt, and external empirical receipts remain open."

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
    ∷ "DASHI.Interop.SensibLawSemanticPromotionPolicy"
    ∷ "DASHI.Core.BoundAcquisitionDemandExact"
    ∷ "DASHI.Cognition.PNF.SensibLawDbNativeCorpusCompilerExact"
    ∷ "DASHI.Law.SensibLawNativeLegalFollowCLIExact"
    ∷ "DASHI.Law.SensibLawPreferredAustralianAuthorityAcquisitionExact"
    ∷ "DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact"
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
    ∷ "Semantic promotion creates no truth authority, legal authority, or generic authority."
    ∷ "Bound acquisition does not pay the requirement or close the consumer."
    ∷ "Producer identity does not identify the residual."
    ∷ "Exact compiler-product reuse does not create semantic admission, authority, applicability, entity identity, proposition identity, event identity, or claim truth."
    ∷ "Native legal-follow orchestration does not create legal authority."
    ∷ "Provider failure is not negative legal evidence."
    ∷ "Expert production does not create truth, legal, admissibility, empirical, clinical, or other authority."
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
    ∷ "The TOE root reaches canonical semantic-authority non-promotion."
    ∷ "The TOE root reaches exact-live bound-acquisition non-promotion."
    ∷ "The TOE root reaches exact compiler-product reuse non-promotion."
    ∷ "The TOE root reaches native legal-follow orchestration non-promotion."
    ∷ "The TOE root reaches provider-access non-evidence and expert-production non-promotion."
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
    ∷ "Resolve exact compiler-product reuse with related/discover/lineage before reuse."
    ∷ [] )
    true refl
    false refl
    false refl
    false refl


------------------------------------------------------------------------
-- Exact compiler-product reuse remains below semantic and legal promotion.
--
-- Reuse the existing SCALE-1 owner.
-- Exact replay is an execution optimisation.
-- It does not create admission, authority, applicability, semantic identity,
-- event identity, proposition identity, or claim truth.
------------------------------------------------------------------------

ExactReuseCreatesSemanticAdmission : Set
ExactReuseCreatesSemanticAdmission =
  DbNative.ExactReuseCreatesSemanticAdmission

ExactReuseCreatesSemanticAuthority : Set
ExactReuseCreatesSemanticAuthority =
  DbNative.ExactReuseCreatesSemanticAuthority

ExactReuseCreatesApplicability : Set
ExactReuseCreatesApplicability =
  DbNative.ExactReuseCreatesApplicability

ExactReuseCreatesEntityIdentity : Set
ExactReuseCreatesEntityIdentity =
  DbNative.ExactReuseCreatesEntityIdentity

ExactReuseCreatesPropositionIdentity : Set
ExactReuseCreatesPropositionIdentity =
  DbNative.ExactReuseCreatesPropositionIdentity

ExactReuseCreatesEventIdentity : Set
ExactReuseCreatesEventIdentity =
  DbNative.ExactReuseCreatesEventIdentity

ExactReuseCreatesClaimTruth : Set
ExactReuseCreatesClaimTruth =
  DbNative.ExactReuseCreatesClaimTruth

toeExactReuseDoesNotCreateSemanticAdmission :
  ExactReuseCreatesSemanticAdmission → ⊥
toeExactReuseDoesNotCreateSemanticAdmission =
  DbNative.exactReuseDoesNotCreateSemanticAdmission

toeExactReuseDoesNotCreateSemanticAuthority :
  ExactReuseCreatesSemanticAuthority → ⊥
toeExactReuseDoesNotCreateSemanticAuthority =
  DbNative.exactReuseDoesNotCreateSemanticAuthority

toeExactReuseDoesNotCreateApplicability :
  ExactReuseCreatesApplicability → ⊥
toeExactReuseDoesNotCreateApplicability =
  DbNative.exactReuseDoesNotCreateApplicability

toeExactReuseDoesNotCreateEntityIdentity :
  ExactReuseCreatesEntityIdentity → ⊥
toeExactReuseDoesNotCreateEntityIdentity =
  DbNative.exactReuseDoesNotCreateEntityIdentity

toeExactReuseDoesNotCreatePropositionIdentity :
  ExactReuseCreatesPropositionIdentity → ⊥
toeExactReuseDoesNotCreatePropositionIdentity =
  DbNative.exactReuseDoesNotCreatePropositionIdentity

toeExactReuseDoesNotCreateEventIdentity :
  ExactReuseCreatesEventIdentity → ⊥
toeExactReuseDoesNotCreateEventIdentity =
  DbNative.exactReuseDoesNotCreateEventIdentity

toeExactReuseDoesNotCreateClaimTruth :
  ExactReuseCreatesClaimTruth → ⊥
toeExactReuseDoesNotCreateClaimTruth =
  DbNative.exactReuseDoesNotCreateClaimTruth



------------------------------------------------------------------------
-- Native legal-follow, provider-access, and expert-production firewalls.
--
-- Reuse exact theorem owners.
-- Orchestration does not create legal authority.
-- Provider failure is not negative legal evidence.
-- Expert production does not create authority.
------------------------------------------------------------------------

NativeCliAutomaticallyLegalAuthority : Set
NativeCliAutomaticallyLegalAuthority =
  NativeLegalFollow.NativeCliAutomaticallyLegalAuthority

ProviderFailureAutomaticallyPropositionFalse : Set
ProviderFailureAutomaticallyPropositionFalse =
  ProviderAcquisition.ProviderFailureAutomaticallyPropositionFalse

toeNativeLegalFollowDoesNotCreateLegalAuthority :
  NativeCliAutomaticallyLegalAuthority → ⊥
toeNativeLegalFollowDoesNotCreateLegalAuthority =
  NativeLegalFollow.nativeCliDoesNotCreateAuthority

toeProviderFailureDoesNotMakePropositionFalse :
  ProviderFailureAutomaticallyPropositionFalse → ⊥
toeProviderFailureDoesNotMakePropositionFalse =
  ProviderAcquisition.providerFailureDoesNotMakePropositionFalse

toeExpertProductionPromotesAnyAuthority :
  Bool
toeExpertProductionPromotesAnyAuthority =
  ExpertProduction.expertProductionPromotesAnyAuthority

toeExpertProductionPromotesAnyAuthorityIsFalse :
  toeExpertProductionPromotesAnyAuthority ≡ false
toeExpertProductionPromotesAnyAuthorityIsFalse =
  ExpertProduction.expertProductionPromotesAnyAuthorityIsFalse

toeNativeLegalFollowCliBoundary :
  NativeLegalFollow.NativeLegalFollowCliBoundary
toeNativeLegalFollowCliBoundary =
  NativeLegalFollow.canonicalNativeLegalFollowCliBoundary

toeProviderFailureCalibration :
  ProviderAcquisition.ProviderFailureCalibration
toeProviderFailureCalibration =
  ProviderAcquisition.canonicalProviderFailureCalibration

toeExpertProductionBoundary :
  ExpertProduction.ExpertProductionBoundary
toeExpertProductionBoundary =
  ExpertProduction.canonicalExpertProductionBoundary


SpacyParserAutomaticallyLegalAuthority : Set
SpacyParserAutomaticallyLegalAuthority =
  NativeLegalFollow.SpacyParserAutomaticallyLegalAuthority

SpacyParserAutomaticallyLegalConstruction : Set
SpacyParserAutomaticallyLegalConstruction =
  NativeLegalFollow.SpacyParserAutomaticallyLegalConstruction

SectionSliceAutomaticallyHistoricalLaw : Set
SectionSliceAutomaticallyHistoricalLaw =
  NativeLegalFollow.SectionSliceAutomaticallyHistoricalLaw

PythonWrapperOwnsLegalSemantics : Set
PythonWrapperOwnsLegalSemantics =
  NativeLegalFollow.PythonWrapperOwnsLegalSemantics

JsonArtifactIsSemanticCommandAbi : Set
JsonArtifactIsSemanticCommandAbi =
  NativeLegalFollow.JsonArtifactIsSemanticCommandAbi

JsonReviewFileAutomaticallyReviewerDecision : Set
JsonReviewFileAutomaticallyReviewerDecision =
  NativeLegalFollow.JsonReviewFileAutomaticallyReviewerDecision

JsonReceiptAutomaticallyClaimTruth : Set
JsonReceiptAutomaticallyClaimTruth =
  NativeLegalFollow.JsonReceiptAutomaticallyClaimTruth

CliSequenceAutomaticallyPaysOpenResidual : Set
CliSequenceAutomaticallyPaysOpenResidual =
  NativeLegalFollow.CliSequenceAutomaticallyPaysOpenResidual

PinnedOalcStreamingAutomaticallyLegalTruth : Set
PinnedOalcStreamingAutomaticallyLegalTruth =
  NativeLegalFollow.PinnedOalcStreamingAutomaticallyLegalTruth

ReviewedHopJsonBecomesCanonicalSemanticTransport : Set
ReviewedHopJsonBecomesCanonicalSemanticTransport =
  NativeLegalFollow.ReviewedHopJsonBecomesCanonicalSemanticTransport

OalcHitAutomaticallyBindingAuthority : Set
OalcHitAutomaticallyBindingAuthority =
  ProviderAcquisition.OalcHitAutomaticallyBindingAuthority

OfficialCourtBytesAutomaticallyPropositionCorrespondence : Set
OfficialCourtBytesAutomaticallyPropositionCorrespondence =
  ProviderAcquisition.OfficialCourtBytesAutomaticallyPropositionCorrespondence

SameMncAutomaticallySameSourceRevision : Set
SameMncAutomaticallySameSourceRevision =
  ProviderAcquisition.SameMncAutomaticallySameSourceRevision

SuccessfulOfficialFetchAutomaticallyProductionReady : Set
SuccessfulOfficialFetchAutomaticallyProductionReady =
  ProviderAcquisition.SuccessfulOfficialFetchAutomaticallyProductionReady

MultipleReportsAutomaticallyIndependent : Set
MultipleReportsAutomaticallyIndependent =
  ExpertProduction.MultipleReportsAutomaticallyIndependent

AgreementAutomaticallyIndependentCorroboration : Set
AgreementAutomaticallyIndependentCorroboration =
  ExpertProduction.AgreementAutomaticallyIndependentCorroboration

DependenceMeansNoEvidence : Set
DependenceMeansNoEvidence =
  ExpertProduction.DependenceMeansNoEvidence

ExpertStatusAutomaticallyTruth : Set
ExpertStatusAutomaticallyTruth =
  ExpertProduction.ExpertStatusAutomaticallyTruth

ReportAdmissionRepairsMissingInput : Set
ReportAdmissionRepairsMissingInput =
  ExpertProduction.ReportAdmissionRepairsMissingInput

CrossExaminationAddsUnobservedInput : Set
CrossExaminationAddsUnobservedInput =
  ExpertProduction.CrossExaminationAddsUnobservedInput

DisputedRiskIsIrrelevant : Set
DisputedRiskIsIrrelevant =
  ExpertProduction.DisputedRiskIsIrrelevant

ObserverDefectMakesOpinionFalse : Set
ObserverDefectMakesOpinionFalse =
  ExpertProduction.ObserverDefectMakesOpinionFalse

QualificationAutomaticallyForensicCompliance : Set
QualificationAutomaticallyForensicCompliance =
  ExpertProduction.QualificationAutomaticallyForensicCompliance

toeSpacyDoesNotCreateLegalAuthority :
  SpacyParserAutomaticallyLegalAuthority → ⊥
toeSpacyDoesNotCreateLegalAuthority =
  NativeLegalFollow.spacyDoesNotCreateLegalAuthority

toeSpacyDoesNotCreateLegalConstruction :
  SpacyParserAutomaticallyLegalConstruction → ⊥
toeSpacyDoesNotCreateLegalConstruction =
  NativeLegalFollow.spacyDoesNotCreateLegalConstruction

toeLatestKnownSectionDoesNotBecomeHistoricalLaw :
  SectionSliceAutomaticallyHistoricalLaw → ⊥
toeLatestKnownSectionDoesNotBecomeHistoricalLaw =
  NativeLegalFollow.latestKnownSectionDoesNotBecomeHistoricalLaw

toePythonWrapperDoesNotOwnLegalSemantics :
  PythonWrapperOwnsLegalSemantics → ⊥
toePythonWrapperDoesNotOwnLegalSemantics =
  NativeLegalFollow.pythonWrapperDoesNotOwnLegalSemantics

toeJsonIsNotSemanticCommandAbi :
  JsonArtifactIsSemanticCommandAbi → ⊥
toeJsonIsNotSemanticCommandAbi =
  NativeLegalFollow.jsonIsNotSemanticCommandAbi

toeJsonReviewDoesNotCreateDecision :
  JsonReviewFileAutomaticallyReviewerDecision → ⊥
toeJsonReviewDoesNotCreateDecision =
  NativeLegalFollow.jsonReviewDoesNotCreateDecision

toeJsonReceiptDoesNotCreateTruth :
  JsonReceiptAutomaticallyClaimTruth → ⊥
toeJsonReceiptDoesNotCreateTruth =
  NativeLegalFollow.jsonReceiptDoesNotCreateTruth

toeCliSequenceDoesNotPayResidual :
  CliSequenceAutomaticallyPaysOpenResidual → ⊥
toeCliSequenceDoesNotPayResidual =
  NativeLegalFollow.cliSequenceDoesNotPayResidual

toePinnedStreamDoesNotCreateLegalTruth :
  PinnedOalcStreamingAutomaticallyLegalTruth → ⊥
toePinnedStreamDoesNotCreateLegalTruth =
  NativeLegalFollow.pinnedStreamDoesNotCreateLegalTruth

toeReviewedHopJsonDoesNotBecomeCanonicalSemanticTransport :
  ReviewedHopJsonBecomesCanonicalSemanticTransport → ⊥
toeReviewedHopJsonDoesNotBecomeCanonicalSemanticTransport =
  NativeLegalFollow.reviewedHopJsonDoesNotBecomeCanonicalSemanticTransport

toeOalcHitDoesNotBecomeBindingAuthority :
  OalcHitAutomaticallyBindingAuthority → ⊥
toeOalcHitDoesNotBecomeBindingAuthority =
  ProviderAcquisition.oalcHitDoesNotBecomeBindingAuthority

toeOfficialCourtBytesDoNotBecomePropositionCorrespondence :
  OfficialCourtBytesAutomaticallyPropositionCorrespondence → ⊥
toeOfficialCourtBytesDoNotBecomePropositionCorrespondence =
  ProviderAcquisition.officialCourtBytesDoNotBecomePropositionCorrespondence

toeSameMncDoesNotCollapseSourceRevisions :
  SameMncAutomaticallySameSourceRevision → ⊥
toeSameMncDoesNotCollapseSourceRevisions =
  ProviderAcquisition.sameMncDoesNotCollapseSourceRevisions

toeSuccessfulOfficialFetchDoesNotBecomeProductionReady :
  SuccessfulOfficialFetchAutomaticallyProductionReady → ⊥
toeSuccessfulOfficialFetchDoesNotBecomeProductionReady =
  ProviderAcquisition.successfulOfficialFetchDoesNotBecomeProductionReady

toeMultipleReportsDoNotAutomaticallyCreateIndependence :
  MultipleReportsAutomaticallyIndependent → ⊥
toeMultipleReportsDoNotAutomaticallyCreateIndependence =
  ExpertProduction.multipleReportsDoNotAutomaticallyCreateIndependence

toeAgreementDoesNotAutomaticallyCreateIndependentCorroboration :
  AgreementAutomaticallyIndependentCorroboration → ⊥
toeAgreementDoesNotAutomaticallyCreateIndependentCorroboration =
  ExpertProduction.agreementDoesNotAutomaticallyCreateIndependentCorroboration

toeDependenceDoesNotMeanNoEvidence :
  DependenceMeansNoEvidence → ⊥
toeDependenceDoesNotMeanNoEvidence =
  ExpertProduction.dependenceDoesNotMeanNoEvidence

toeExpertStatusDoesNotAutomaticallyCreateTruth :
  ExpertStatusAutomaticallyTruth → ⊥
toeExpertStatusDoesNotAutomaticallyCreateTruth =
  ExpertProduction.expertStatusDoesNotAutomaticallyCreateTruth

toeReportAdmissionDoesNotRepairMissingInput :
  ReportAdmissionRepairsMissingInput → ⊥
toeReportAdmissionDoesNotRepairMissingInput =
  ExpertProduction.reportAdmissionDoesNotRepairMissingInput

toeCrossExaminationDoesNotAddUnobservedInput :
  CrossExaminationAddsUnobservedInput → ⊥
toeCrossExaminationDoesNotAddUnobservedInput =
  ExpertProduction.crossExaminationDoesNotAddUnobservedInput

toeDisputedRiskDoesNotBecomeIrrelevant :
  DisputedRiskIsIrrelevant → ⊥
toeDisputedRiskDoesNotBecomeIrrelevant =
  ExpertProduction.disputedRiskDoesNotBecomeIrrelevant

toeObserverDefectDoesNotProveOpinionFalse :
  ObserverDefectMakesOpinionFalse → ⊥
toeObserverDefectDoesNotProveOpinionFalse =
  ExpertProduction.observerDefectDoesNotProveOpinionFalse

toeQualificationDoesNotAutomaticallyProveForensicCompliance :
  QualificationAutomaticallyForensicCompliance → ⊥
toeQualificationDoesNotAutomaticallyProveForensicCompliance =
  ExpertProduction.qualificationDoesNotAutomaticallyProveForensicCompliance

toeLegalReviewDoesNotCreateClaimTruth :
  LegalReviewDecisionCreatesClaimTruth → ⊥
toeLegalReviewDoesNotCreateClaimTruth =
  RealMatterReview.legalReviewDecisionDoesNotCreateClaimTruth

toeOfficialLegalSurfaceDoesNotRecoverFineState :
  OfficialLegalSurfaceRecoversFineState → ⊥
toeOfficialLegalSurfaceDoesNotRecoverFineState =
  LegalDecision.officialSurfaceCannotRecoverFineLegalState

toeOfficialActionDoesNotRecoverAutonomyAndAuthority :
  NF.FactorsThrough
    LegalDecision.autonomyOfficialSurface
    LegalDecision.fineAutonomyLegalStateOf
  → ⊥
toeOfficialActionDoesNotRecoverAutonomyAndAuthority =
  LegalDecision.officialActionCannotRecoverAutonomyAndAuthority

toeLegalityAloneDoesNotCreateLegitimacy :
  LegalOnlyCreatesLegitimacy → ⊥
toeLegalityAloneDoesNotCreateLegitimacy =
  Legitimacy.legalOnlyIsNotAdmittedLegitimacy

toeMissingAdmissibilityStillAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true false true true true)
  ≡ Governed.abstain
toeMissingAdmissibilityStillAbstains =
  Promotion.missingAdmissibilityAbstains

toeMissingValidationStillAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true true true true false)
  ≡ Governed.abstain
toeMissingValidationStillAbstains =
  Promotion.missingValidationAbstains

toeActionstepStyleVendorIdentityCreatesAuthority :
  Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority
    Domain.canonicalDomainTransportReceipt
  ≡ false
toeActionstepStyleVendorIdentityCreatesAuthority = refl

toeActionstepStyleTargetNeedsOwnAuthorityWitness :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
    Domain.canonicalDomainTransportReceipt
  ≡ true
toeActionstepStyleTargetNeedsOwnAuthorityWitness = refl

------------------------------------------------------------------------
-- Canonical governance invariant handoff.
--
-- This record unifies existing exact proof owners.
-- It adds no new legal semantics.
-- It adds no new authority.
-- It keeps the ZKP control receipt, governance boundaries, and non-promotion
-- theorems on one same-object TOE surface.
------------------------------------------------------------------------

record GovernedLegalWorkflowTOEInvariantHandoff : Set₁ where
  constructor governed-legal-workflow-toe-invariant-handoff
  field
    governanceBoundary :
      GovernedLegalWorkflowTOEBoundary

    governanceBoundaryIsCanonical :
      governanceBoundary
      ≡
      canonicalGovernedLegalWorkflowTOEBoundary

    promotionBoundary :
      GovernedLegalWorkflowPromotionBoundary

    promotionBoundaryIsCanonical :
      promotionBoundary
      ≡
      canonicalGovernedLegalWorkflowPromotionBoundary

    zkpReceipt :
      GovernedLegalWorkflowZKPReceipt

    zkpReceiptIsCanonical :
      zkpReceipt
      ≡
      canonicalGovernedLegalWorkflowZKPReceipt

    introspectiveZKPFrame :
      GovernedLegalWorkflowIntrospectiveZKPFrame

    introspectiveZKPFrameIsCanonical :
      introspectiveZKPFrame
      ≡
      canonicalGovernedLegalWorkflowIntrospectiveZKPFrame

    taskCompletionNonPromotion :
      TaskCompletionCreatesTruth →
      ⊥

    databaseCommitNonPromotion :
      DatabaseCommitCreatesSemanticAuthority →
      ⊥

    acceptedReviewApplicabilityFirewall :
      AcceptedStatusPaysApplicability →
      ⊥

    reviewEligibilityPromotionFirewall :
      ReviewEligibilityCreatesPromotionReceipt →
      ⊥

    runtimeParityTruthFirewall :
      ZeroParityFailuresMeansWorldTruth →
      ⊥

    parserAdmissionFirewall :
      ParserCandidateAloneAuthorizesAdmission →
      ⊥

    softwarePublicationFirewall :
      SoftwareValidationAuthorizesPublication →
      ⊥

    semanticPromotionTruthAuthorityClosed :
      AuthorityNonPromotion.truthAuthorityFlag
        SemanticPromotion.semanticPromotionAuthorityBoundary
      ≡ false

    semanticPromotionLegalAuthorityClosed :
      AuthorityNonPromotion.legalAuthorityFlag
        SemanticPromotion.semanticPromotionAuthorityBoundary
      ≡ false

    semanticPromotionAllAuthorityClosed :
      AuthorityNonPromotion.promotesAnyAuthority
        SemanticPromotion.semanticPromotionAuthorityBoundary
      ≡ false

    boundAcquisitionPaymentFirewall :
      BoundDemandAutomaticallyPaysRequirement →
      ⊥

    boundAcquisitionClosureFirewall :
      BoundDemandAutomaticallyClosesConsumer →
      ⊥

    producerIdentityResidualFirewall :
      SameProducerIdentifiesResidual →
      ⊥

    caseySelectionTruthFirewall :
      CaseySelectionCreatesWorldTruth →
      ⊥

    formalProofExternalTruthFirewall :
      Suite.FormalProofCreatesExternalWorldTruth →
      ⊥

    knowledgeExecutionAuthorityFirewall :
      KnowledgeIsAuthority →
      ⊥

    nativeLegalFollowAuthorityFirewall :
      NativeCliAutomaticallyLegalAuthority →
      ⊥

    providerFailureNegativeEvidenceFirewall :
      ProviderFailureAutomaticallyPropositionFalse →
      ⊥

    expertProductionAuthorityClosed :
      toeExpertProductionPromotesAnyAuthority ≡ false

    spacyLegalAuthorityFirewall :
      SpacyParserAutomaticallyLegalAuthority → ⊥

    spacyLegalConstructionFirewall :
      SpacyParserAutomaticallyLegalConstruction → ⊥

    latestSectionHistoricalLawFirewall :
      SectionSliceAutomaticallyHistoricalLaw → ⊥

    pythonLegalSemanticsFirewall :
      PythonWrapperOwnsLegalSemantics → ⊥

    jsonSemanticCommandFirewall :
      JsonArtifactIsSemanticCommandAbi → ⊥

    jsonReviewDecisionFirewall :
      JsonReviewFileAutomaticallyReviewerDecision → ⊥

    jsonClaimTruthFirewall :
      JsonReceiptAutomaticallyClaimTruth → ⊥

    cliResidualPaymentFirewall :
      CliSequenceAutomaticallyPaysOpenResidual → ⊥

    pinnedStreamLegalTruthFirewall :
      PinnedOalcStreamingAutomaticallyLegalTruth → ⊥

    reviewedHopJsonSemanticTransportFirewall :
      ReviewedHopJsonBecomesCanonicalSemanticTransport → ⊥

    oalcBindingAuthorityFirewall :
      OalcHitAutomaticallyBindingAuthority → ⊥

    officialBytesCorrespondenceFirewall :
      OfficialCourtBytesAutomaticallyPropositionCorrespondence → ⊥

    sourceRevisionCollapseFirewall :
      SameMncAutomaticallySameSourceRevision → ⊥

    officialFetchProductionReadinessFirewall :
      SuccessfulOfficialFetchAutomaticallyProductionReady → ⊥

    reportMultiplicityIndependenceFirewall :
      MultipleReportsAutomaticallyIndependent → ⊥

    agreementIndependentCorroborationFirewall :
      AgreementAutomaticallyIndependentCorroboration → ⊥

    dependenceNoEvidenceFirewall :
      DependenceMeansNoEvidence → ⊥

    expertStatusTruthFirewall :
      ExpertStatusAutomaticallyTruth → ⊥

    reportAdmissionRepairFirewall :
      ReportAdmissionRepairsMissingInput → ⊥

    crossExaminationObservationFirewall :
      CrossExaminationAddsUnobservedInput → ⊥

    disputedRiskRelevanceFirewall :
      DisputedRiskIsIrrelevant → ⊥

    observerDefectTruthFirewall :
      ObserverDefectMakesOpinionFalse → ⊥

    qualificationForensicComplianceFirewall :
      QualificationAutomaticallyForensicCompliance → ⊥

    legalReviewTruthFirewall :
      LegalReviewDecisionCreatesClaimTruth → ⊥

    officialSurfaceFineStateFirewall :
      OfficialLegalSurfaceRecoversFineState → ⊥

    officialActionAutonomyAuthorityFirewall :
      NF.FactorsThrough
        LegalDecision.autonomyOfficialSurface
        LegalDecision.fineAutonomyLegalStateOf
      → ⊥

    legalityLegitimacyFirewall :
      LegalOnlyCreatesLegitimacy → ⊥

    missingAdmissibilityAbstention :
      Promotion.authorizationFromObligations
        (Canonical.promotionObligations true false true true true)
      ≡ Governed.abstain

    missingValidationAbstention :
      Promotion.authorizationFromObligations
        (Canonical.promotionObligations true true true true false)
      ≡ Governed.abstain

    actionstepStyleVendorAuthorityFirewall :
      Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority
        Domain.canonicalDomainTransportReceipt
      ≡ false

    actionstepStyleTargetAuthorityWitnessRequired :
      Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
        Domain.canonicalDomainTransportReceipt
      ≡ true

    exactReuseAdmissionFirewall :
      ExactReuseCreatesSemanticAdmission →
      ⊥

    exactReuseAuthorityFirewall :
      ExactReuseCreatesSemanticAuthority →
      ⊥

    exactReuseApplicabilityFirewall :
      ExactReuseCreatesApplicability →
      ⊥

    exactReuseEntityIdentityFirewall :
      ExactReuseCreatesEntityIdentity →
      ⊥

    exactReusePropositionIdentityFirewall :
      ExactReuseCreatesPropositionIdentity →
      ⊥

    exactReuseEventIdentityFirewall :
      ExactReuseCreatesEventIdentity →
      ⊥

    exactReuseClaimTruthFirewall :
      ExactReuseCreatesClaimTruth →
      ⊥

open GovernedLegalWorkflowTOEInvariantHandoff public

canonicalGovernedLegalWorkflowTOEInvariantHandoff :
  GovernedLegalWorkflowTOEInvariantHandoff
canonicalGovernedLegalWorkflowTOEInvariantHandoff =
  governed-legal-workflow-toe-invariant-handoff
    canonicalGovernedLegalWorkflowTOEBoundary
    refl
    canonicalGovernedLegalWorkflowPromotionBoundary
    refl
    canonicalGovernedLegalWorkflowZKPReceipt
    refl
    canonicalGovernedLegalWorkflowIntrospectiveZKPFrame
    refl
    toeTaskCompletionDoesNotCreateTruth
    toeDatabaseCommitDoesNotCreateSemanticAuthority
    toeAcceptedReviewDoesNotPayApplicability
    toeReviewEligibilityDoesNotCreatePromotion
    toeRuntimeParityDoesNotCreateWorldTruth
    toeParserCandidateDoesNotAuthorizeAdmission
    toeSoftwareValidationDoesNotAuthorizePublication
    toeSemanticPromotionTruthAuthorityClosed
    toeSemanticPromotionLegalAuthorityClosed
    toeSemanticPromotionAllAuthorityClosed
    toeBoundAcquisitionDoesNotPayRequirement
    toeBoundAcquisitionDoesNotCloseConsumer
    toeProducerIdentityDoesNotIdentifyResidual
    toeCaseySelectionDoesNotCreateWorldTruth
    toeFormalProofDoesNotCreateExternalWorldTruth
    toeKnowledgeDoesNotCreateExecutionAuthority
    toeNativeLegalFollowDoesNotCreateLegalAuthority
    toeProviderFailureDoesNotMakePropositionFalse
    toeExpertProductionPromotesAnyAuthorityIsFalse
    toeSpacyDoesNotCreateLegalAuthority
    toeSpacyDoesNotCreateLegalConstruction
    toeLatestKnownSectionDoesNotBecomeHistoricalLaw
    toePythonWrapperDoesNotOwnLegalSemantics
    toeJsonIsNotSemanticCommandAbi
    toeJsonReviewDoesNotCreateDecision
    toeJsonReceiptDoesNotCreateTruth
    toeCliSequenceDoesNotPayResidual
    toePinnedStreamDoesNotCreateLegalTruth
    toeReviewedHopJsonDoesNotBecomeCanonicalSemanticTransport
    toeOalcHitDoesNotBecomeBindingAuthority
    toeOfficialCourtBytesDoNotBecomePropositionCorrespondence
    toeSameMncDoesNotCollapseSourceRevisions
    toeSuccessfulOfficialFetchDoesNotBecomeProductionReady
    toeMultipleReportsDoNotAutomaticallyCreateIndependence
    toeAgreementDoesNotAutomaticallyCreateIndependentCorroboration
    toeDependenceDoesNotMeanNoEvidence
    toeExpertStatusDoesNotAutomaticallyCreateTruth
    toeReportAdmissionDoesNotRepairMissingInput
    toeCrossExaminationDoesNotAddUnobservedInput
    toeDisputedRiskDoesNotBecomeIrrelevant
    toeObserverDefectDoesNotProveOpinionFalse
    toeQualificationDoesNotAutomaticallyProveForensicCompliance
    toeLegalReviewDoesNotCreateClaimTruth
    toeOfficialLegalSurfaceDoesNotRecoverFineState
    toeOfficialActionDoesNotRecoverAutonomyAndAuthority
    toeLegalityAloneDoesNotCreateLegitimacy
    toeMissingAdmissibilityStillAbstains
    toeMissingValidationStillAbstains
    toeActionstepStyleVendorIdentityCreatesAuthority
    toeActionstepStyleTargetNeedsOwnAuthorityWitness
    toeExactReuseDoesNotCreateSemanticAdmission
    toeExactReuseDoesNotCreateSemanticAuthority
    toeExactReuseDoesNotCreateApplicability
    toeExactReuseDoesNotCreateEntityIdentity
    toeExactReuseDoesNotCreatePropositionIdentity
    toeExactReuseDoesNotCreateEventIdentity
    toeExactReuseDoesNotCreateClaimTruth

toeProcessContextRefs : List String
toeProcessContextRefs =
  "meta-introspector/zkperf — process and tooling context; no theorem copied"
  ∷ "meta-introspector/zos-server — reconciliation/runtime context; original attribution retained"
  ∷ "meta-introspector/erdfa-py — process/tooling context; original attribution retained"
  ∷ "meta-introspector/aristotle-cli-rs — proof-project tooling context; original attribution retained"
  ∷ "chboishabba/zkSEC — authority/receipt process context; no theorem copied"
  ∷ []


------------------------------------------------------------------------
-- Reuse legal-source authority and applicability non-promotion.
-- An Actionstep-style matter action is not a legal authority certificate.
------------------------------------------------------------------------

toeCandidateSourceDoesNotCloseAuthority :
  LegalAuthority.CandidateSourceIsAuthoritative → ⊥
toeCandidateSourceDoesNotCloseAuthority =
  LegalAuthority.candidateSourceDoesNotCloseAuthority

toeSameSystemDoesNotAutomaticallyCloseAuthority :
  LegalAuthority.SameLegalSystemAutomaticallyMeansAuthority → ⊥
toeSameSystemDoesNotAutomaticallyCloseAuthority =
  LegalAuthority.sameSystemDoesNotAutomaticallyCloseAuthority

toeCurrentValidityDoesNotAutomaticallyEstablishApplicability :
  LegalAuthority.CurrentValidityAutomaticallyMeansApplicability → ⊥
toeCurrentValidityDoesNotAutomaticallyEstablishApplicability =
  LegalAuthority.currentValidityDoesNotAutomaticallyEstablishApplicability

toeSemanticAdmissionDoesNotBecomeLegalSourceAuthority :
  LegalAuthority.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
toeSemanticAdmissionDoesNotBecomeLegalSourceAuthority =
  LegalAuthority.semanticAdmissionDoesNotBecomeLegalSourceAuthority

toeDocumentRoleDoesNotSupplyLegalSourceAuthority :
  LegalAuthority.DocumentRoleSuppliesLegalSourceAuthority → ⊥
toeDocumentRoleDoesNotSupplyLegalSourceAuthority =
  LegalAuthority.documentRoleDoesNotSupplyLegalSourceAuthority

toeCanonicalLegalSourceAuthorityBoundary :
  LegalAuthority.LegalSourceAuthorityBoundary
toeCanonicalLegalSourceAuthorityBoundary =
  LegalAuthority.canonicalLegalSourceAuthorityBoundary


CandidateSourceIsAuthoritative : Set
CandidateSourceIsAuthoritative = LegalAuthority.CandidateSourceIsAuthoritative

CurrentValidityAutomaticallyMeansApplicability : Set
CurrentValidityAutomaticallyMeansApplicability =
  LegalAuthority.CurrentValidityAutomaticallyMeansApplicability

SemanticAdmissionAuthorityIsLegalSourceAuthority : Set
SemanticAdmissionAuthorityIsLegalSourceAuthority =
  LegalAuthority.SemanticAdmissionAuthorityIsLegalSourceAuthority

------------------------------------------------------------------------
-- Legal-source authority type aliases required by normalized handoffs.
------------------------------------------------------------------------

SameLegalSystemAutomaticallyMeansAuthority : Set
SameLegalSystemAutomaticallyMeansAuthority =
  LegalAuthority.SameLegalSystemAutomaticallyMeansAuthority

DocumentRoleSuppliesLegalSourceAuthority : Set
DocumentRoleSuppliesLegalSourceAuthority =
  LegalAuthority.DocumentRoleSuppliesLegalSourceAuthority
