module DASHI.Unified.GovernedLegalWorkflowTOEBridgeRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as Bridge
import DASHI.Unifier as Unifier

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
