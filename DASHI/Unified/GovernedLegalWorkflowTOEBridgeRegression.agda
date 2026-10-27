module DASHI.Unified.GovernedLegalWorkflowTOEBridgeRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as Bridge
import DASHI.Unifier as Unifier

unifierUsesCanonicalInvariantHandoff :
  Unifier.toeGovernedLegalWorkflowInvariantHandoff
  ≡
  Bridge.canonicalGovernedLegalWorkflowTOEInvariantHandoff
unifierUsesCanonicalInvariantHandoff =
  refl

invariantHandoffUsesCanonicalGovernanceBoundary :
  Bridge.governanceBoundary
    Unifier.toeGovernedLegalWorkflowInvariantHandoff
  ≡
  Bridge.canonicalGovernedLegalWorkflowTOEBoundary
invariantHandoffUsesCanonicalGovernanceBoundary =
  Bridge.governanceBoundaryIsCanonical
    Unifier.toeGovernedLegalWorkflowInvariantHandoff

invariantHandoffUsesCanonicalPromotionBoundary :
  Bridge.promotionBoundary
    Unifier.toeGovernedLegalWorkflowInvariantHandoff
  ≡
  Bridge.canonicalGovernedLegalWorkflowPromotionBoundary
invariantHandoffUsesCanonicalPromotionBoundary =
  Bridge.promotionBoundaryIsCanonical
    Unifier.toeGovernedLegalWorkflowInvariantHandoff

invariantHandoffUsesCanonicalZKPReceipt :
  Bridge.zkpReceipt
    Unifier.toeGovernedLegalWorkflowInvariantHandoff
  ≡
  Bridge.canonicalGovernedLegalWorkflowZKPReceipt
invariantHandoffUsesCanonicalZKPReceipt =
  Bridge.zkpReceiptIsCanonical
    Unifier.toeGovernedLegalWorkflowInvariantHandoff

unifierUsesCanonicalGovernedLegalWorkflowBoundary :
  Unifier.toeGovernedLegalWorkflowBoundary
  ≡ Bridge.canonicalGovernedLegalWorkflowTOEBoundary
unifierUsesCanonicalGovernedLegalWorkflowBoundary = refl

workflowCompletionStillDoesNotCreateTruth :
  Bridge.operationalCompletionCreatesTruth
    Unifier.toeGovernedLegalWorkflowBoundary
  ≡ false
workflowCompletionStillDoesNotCreateTruth = refl

databaseCommitStillDoesNotCreateSemanticAuthority :
  Bridge.databaseCommitCreatesSemanticAuthority
    Unifier.toeGovernedLegalWorkflowBoundary
  ≡ false
databaseCommitStillDoesNotCreateSemanticAuthority = refl

acceptedReviewStillDoesNotPayApplicability :
  Bridge.acceptedReviewPaysApplicability
    Unifier.toeGovernedLegalWorkflowBoundary
  ≡ false
acceptedReviewStillDoesNotPayApplicability = refl

controlEvidenceStillDoesNotCreateTruth :
  Bridge.controlEvidenceCreatesTruth
    Unifier.toeGovernedLegalWorkflowBoundary
  ≡ false
controlEvidenceStillDoesNotCreateTruth = refl

passingControlStillDoesNotMeanCertification :
  Bridge.passingControlMeansCertification
    Unifier.toeGovernedLegalWorkflowBoundary
  ≡ false
passingControlStillDoesNotMeanCertification = refl

citationStillDoesNotRealiseLegalRule :
  Bridge.citationAloneRealisesLegalRule
    Unifier.toeGovernedLegalWorkflowBoundary
  ≡ false
citationStillDoesNotRealiseLegalRule = refl

semanticMeetStillDoesNotProveApplicability :
  Bridge.semanticMeetAloneProvesApplicability
    Unifier.toeGovernedLegalWorkflowBoundary
  ≡ false
semanticMeetStillDoesNotProveApplicability = refl

kernelClosureStillDoesNotMeanSemanticClosure :
  Bridge.kernelClosureMeansSemanticClosure
    Unifier.toeGovernedLegalWorkflowBoundary
  ≡ false
kernelClosureStillDoesNotMeanSemanticClosure = refl

unifierTaskCompletionAliasIsExact :
  Bridge.TaskCompletionCreatesTruth → ⊥
unifierTaskCompletionAliasIsExact =
  Unifier.toeWorkflowTaskCompletionDoesNotCreateTruth

unifierReviewApplicabilityAliasIsExact :
  Bridge.AcceptedStatusPaysApplicability → ⊥
unifierReviewApplicabilityAliasIsExact =
  Unifier.toeAcceptedReviewDoesNotPayApplicability

unifierControlCertificationAliasIsExact :
  Bridge.PassingControlMeansCertified → ⊥
unifierControlCertificationAliasIsExact =
  Unifier.toePassingControlDoesNotMeanCertified


unifierUsesCanonicalZKPReceipt :
  Unifier.toeGovernedLegalWorkflowZKPReceipt
  ≡ Bridge.canonicalGovernedLegalWorkflowZKPReceipt
unifierUsesCanonicalZKPReceipt = refl

unifierUsesCanonicalIntrospectiveZKPFrame :
  Unifier.toeGovernedLegalWorkflowIntrospectiveZKPFrame
  ≡ Bridge.canonicalGovernedLegalWorkflowIntrospectiveZKPFrame
unifierUsesCanonicalIntrospectiveZKPFrame = refl

invariantHandoffUsesCanonicalIntrospectiveZKPFrame :
  Bridge.introspectiveZKPFrame
    Unifier.toeGovernedLegalWorkflowInvariantHandoff
  ≡
  Bridge.canonicalGovernedLegalWorkflowIntrospectiveZKPFrame
invariantHandoffUsesCanonicalIntrospectiveZKPFrame =
  Bridge.introspectiveZKPFrameIsCanonical
    Unifier.toeGovernedLegalWorkflowInvariantHandoff

zkpStandardsRemainDesignLenses :
  Bridge.standardsAreDesignLenses
    Unifier.toeGovernedLegalWorkflowZKPReceipt
  ≡ true
zkpStandardsRemainDesignLenses = refl

zkpStandardsDoNotClaimCertification :
  Bridge.standardsCertificationClaimed
    Unifier.toeGovernedLegalWorkflowZKPReceipt
  ≡ false
zkpStandardsDoNotClaimCertification = refl

zkpESDSurfaceMutationRemainsForbidden :
  Bridge.esdSurfaceMutationAllowed
    Unifier.toeGovernedLegalWorkflowZKPReceipt
  ≡ false
zkpESDSurfaceMutationRemainsForbidden = refl

unifierCaseyAuthorityAliasIsExact :
  Bridge.CaseySelectionCreatesWorldTruth → ⊥
unifierCaseyAuthorityAliasIsExact =
  Unifier.toeCaseySelectionDoesNotCreateWorldTruth

unifierKnowledgeAuthorityAliasIsExact :
  Bridge.KnowledgeIsAuthority → ⊥
unifierKnowledgeAuthorityAliasIsExact =
  Unifier.toeKnowledgeDoesNotCreateExecutionAuthority


------------------------------------------------------------------------
-- Promotion, validation, and admission regression.
------------------------------------------------------------------------

unifierUsesCanonicalPromotionBoundary :
  Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ Bridge.canonicalGovernedLegalWorkflowPromotionBoundary
unifierUsesCanonicalPromotionBoundary = refl

reviewEligibilityStillDoesNotCreatePromotion :
  Bridge.reviewEligibilityCreatesPromotion
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
reviewEligibilityStillDoesNotCreatePromotion = refl

runtimeParityStillDoesNotCreateWorldTruth :
  Bridge.runtimeParityCreatesWorldTruth
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
runtimeParityStillDoesNotCreateWorldTruth = refl

diagnosticStreamStillDoesNotCreateLegalCertification :
  Bridge.diagnosticStreamCreatesLegalCertification
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
diagnosticStreamStillDoesNotCreateLegalCertification = refl

claimProjectionStillDoesNotCreateTruth :
  Bridge.claimProjectionCreatesTruth
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
claimProjectionStillDoesNotCreateTruth = refl

reviewRouterStillDoesNotCreateAdequacy :
  Bridge.reviewRouterCreatesConsumerAdequacy
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
reviewRouterStillDoesNotCreateAdequacy = refl

parserCandidateStillDoesNotAuthorizeAdmission :
  Bridge.parserCandidateCreatesAdmissionAuthority
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
parserCandidateStillDoesNotAuthorizeAdmission = refl

residualPriorityStillDoesNotCreateTruthConfidence :
  Bridge.residualPriorityCreatesTruthConfidence
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
residualPriorityStillDoesNotCreateTruthConfidence = refl

admissionReceiptStillDoesNotCreatePublication :
  Bridge.admissionReceiptCreatesPublicationAuthority
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
admissionReceiptStillDoesNotCreatePublication = refl

softwareValidationStillDoesNotCreatePublication :
  Bridge.softwareValidationCreatesPublicationAuthority
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
softwareValidationStillDoesNotCreatePublication = refl

laterValidationStillDoesNotRewriteBaseline :
  Bridge.laterValidationRewritesCertifiedBaseline
    Unifier.toeGovernedLegalWorkflowPromotionBoundary
  ≡ false
laterValidationStillDoesNotRewriteBaseline = refl

unifierReviewEligibilityAliasIsExact :
  Bridge.ReviewEligibilityCreatesPromotionReceipt → ⊥
unifierReviewEligibilityAliasIsExact =
  Unifier.toeReviewEligibilityDoesNotCreatePromotion

unifierRuntimeParityAliasIsExact :
  Bridge.ZeroParityFailuresMeansWorldTruth → ⊥
unifierRuntimeParityAliasIsExact =
  Unifier.toeRuntimeParityDoesNotCreateWorldTruth

unifierAdmissionAliasIsExact :
  Bridge.ParserCandidateAloneAuthorizesAdmission → ⊥
unifierAdmissionAliasIsExact =
  Unifier.toeParserCandidateDoesNotAuthorizeAdmission

unifierSoftwarePublicationAliasIsExact :
  Bridge.SoftwareValidationAuthorizesPublication → ⊥
unifierSoftwarePublicationAliasIsExact =
  Unifier.toeSoftwareValidationDoesNotAuthorizePublication


------------------------------------------------------------------------
-- Canonical semantic-authority and exact-live acquisition regressions.
------------------------------------------------------------------------

unifierSemanticPromotionTruthAuthorityAliasIsExact :
  Bridge.SemanticPromotionTruthAuthorityClosed
unifierSemanticPromotionTruthAuthorityAliasIsExact =
  Unifier.toeSemanticPromotionTruthAuthorityClosed

unifierSemanticPromotionLegalAuthorityAliasIsExact :
  Bridge.SemanticPromotionLegalAuthorityClosed
unifierSemanticPromotionLegalAuthorityAliasIsExact =
  Unifier.toeSemanticPromotionLegalAuthorityClosed

unifierSemanticPromotionAllAuthorityAliasIsExact :
  Bridge.SemanticPromotionAllAuthorityClosed
unifierSemanticPromotionAllAuthorityAliasIsExact =
  Unifier.toeSemanticPromotionAllAuthorityClosed

unifierBoundAcquisitionPaymentAliasIsExact :
  Bridge.BoundDemandAutomaticallyPaysRequirement → ⊥
unifierBoundAcquisitionPaymentAliasIsExact =
  Unifier.toeBoundAcquisitionDoesNotPayRequirement

unifierBoundAcquisitionClosureAliasIsExact :
  Bridge.BoundDemandAutomaticallyClosesConsumer → ⊥
unifierBoundAcquisitionClosureAliasIsExact =
  Unifier.toeBoundAcquisitionDoesNotCloseConsumer

unifierProducerIdentityResidualAliasIsExact :
  Bridge.SameProducerIdentifiesResidual → ⊥
unifierProducerIdentityResidualAliasIsExact =
  Unifier.toeProducerIdentityDoesNotIdentifyResidual


-- Exact aliases cannot create new legal-source authority.
unifierLegalCandidateIsNotAuthority :
  Bridge.CandidateSourceIsAuthoritative → ⊥
unifierLegalCandidateIsNotAuthority =
  Unifier.unifierLegalCandidateIsNotAuthority

unifierLegalValidityIsNotApplicability :
  Bridge.CurrentValidityAutomaticallyMeansApplicability → ⊥
unifierLegalValidityIsNotApplicability =
  Unifier.unifierLegalValidityIsNotApplicability

unifierSemanticAdmissionIsNotLegalAuthority :
  Bridge.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
unifierSemanticAdmissionIsNotLegalAuthority =
  Unifier.unifierSemanticAdmissionIsNotLegalAuthority


------------------------------------------------------------------------
-- Legal-source authority invariant handoff regression.
------------------------------------------------------------------------

unifierUsesCanonicalAuthorityInvariantHandoff :
  Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff
  ≡
  Bridge.canonicalGovernedLegalWorkflowAuthorityInvariantHandoff
unifierUsesCanonicalAuthorityInvariantHandoff = refl

authorityHandoffUsesCanonicalWorkflowHandoff :
  Bridge.workflowInvariantHandoff
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff
  ≡
  Bridge.canonicalGovernedLegalWorkflowTOEInvariantHandoff
authorityHandoffUsesCanonicalWorkflowHandoff =
  Bridge.workflowInvariantHandoffIsCanonical
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff

authorityHandoffUsesCanonicalLegalSourceBoundary :
  Bridge.legalSourceAuthorityBoundary
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff
  ≡
  Bridge.toeCanonicalLegalSourceAuthorityBoundary
authorityHandoffUsesCanonicalLegalSourceBoundary =
  Bridge.legalSourceAuthorityBoundaryIsCanonical
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff

authorityHandoffCandidateFirewallIsExact :
  Bridge.CandidateSourceIsAuthoritative → ⊥
authorityHandoffCandidateFirewallIsExact =
  Bridge.candidateSourceAuthorityFirewall
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff

authorityHandoffSameSystemFirewallIsExact :
  Bridge.SameLegalSystemAutomaticallyMeansAuthority → ⊥
authorityHandoffSameSystemFirewallIsExact =
  Bridge.sameSystemAuthorityFirewall
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff

authorityHandoffValidityFirewallIsExact :
  Bridge.CurrentValidityAutomaticallyMeansApplicability → ⊥
authorityHandoffValidityFirewallIsExact =
  Bridge.currentValidityApplicabilityFirewall
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff

authorityHandoffAdmissionFirewallIsExact :
  Bridge.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
authorityHandoffAdmissionFirewallIsExact =
  Bridge.semanticAdmissionAuthorityFirewall
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff

authorityHandoffDocumentRoleFirewallIsExact :
  Bridge.DocumentRoleSuppliesLegalSourceAuthority → ⊥
authorityHandoffDocumentRoleFirewallIsExact =
  Bridge.documentRoleAuthorityFirewall
    Unifier.unifierGovernedLegalWorkflowAuthorityInvariantHandoff
