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
-- This comment-only child commit triggers the exact-head verification PR.
-- Exact-head kernel certification remains a separate receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
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
