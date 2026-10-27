{-# OPTIONS --safe #-}
module DASHI.Unified.GovernedLegalWorkflowTOEBridgeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as Bridge
import DASHI.Unifier as Unifier

unifierUsesCanonicalInvariantHandoff :
  Unifier.unifierGovernedLegalWorkflowInvariantHandoff
  ≡ Bridge.canonicalGovernedLegalWorkflowTOEInvariantHandoff
unifierUsesCanonicalInvariantHandoff = refl

invariantHandoffUsesCanonicalGovernanceBoundary :
  Bridge.governanceBoundary
    Unifier.unifierGovernedLegalWorkflowInvariantHandoff
  ≡ Bridge.canonicalGovernedLegalWorkflowTOEBoundary
invariantHandoffUsesCanonicalGovernanceBoundary =
  Bridge.governanceBoundaryIsCanonical
    Unifier.unifierGovernedLegalWorkflowInvariantHandoff

invariantHandoffUsesCanonicalPromotionBoundary :
  Bridge.promotionBoundary
    Unifier.unifierGovernedLegalWorkflowInvariantHandoff
  ≡ Bridge.canonicalGovernedLegalWorkflowPromotionBoundary
invariantHandoffUsesCanonicalPromotionBoundary =
  Bridge.promotionBoundaryIsCanonical
    Unifier.unifierGovernedLegalWorkflowInvariantHandoff

invariantHandoffUsesCanonicalZKPReceipt :
  Bridge.zkpReceipt
    Unifier.unifierGovernedLegalWorkflowInvariantHandoff
  ≡ Bridge.canonicalGovernedLegalWorkflowZKPReceipt
invariantHandoffUsesCanonicalZKPReceipt =
  Bridge.zkpReceiptIsCanonical
    Unifier.unifierGovernedLegalWorkflowInvariantHandoff

zkpStandardsRemainDesignLenses :
  Bridge.standardsAreDesignLenses
    Bridge.canonicalGovernedLegalWorkflowZKPReceipt
  ≡ true
zkpStandardsRemainDesignLenses = refl

zkpStandardsDoNotClaimCertification :
  Bridge.standardsCertificationClaimed
    Bridge.canonicalGovernedLegalWorkflowZKPReceipt
  ≡ false
zkpStandardsDoNotClaimCertification = refl

zkpESDSurfaceMutationRemainsForbidden :
  Bridge.esdSurfaceMutationAllowed
    Bridge.canonicalGovernedLegalWorkflowZKPReceipt
  ≡ false
zkpESDSurfaceMutationRemainsForbidden = refl

unifierTaskCompletionAliasIsExact :
  Bridge.TaskCompletionCreatesTruth → ⊥
unifierTaskCompletionAliasIsExact =
  Unifier.unifierTaskCompletionDoesNotCreateTruth

unifierDatabaseAuthorityAliasIsExact :
  Bridge.DatabaseCommitCreatesSemanticAuthority → ⊥
unifierDatabaseAuthorityAliasIsExact =
  Unifier.unifierDatabaseCommitDoesNotCreateSemanticAuthority

unifierReviewApplicabilityAliasIsExact :
  Bridge.AcceptedStatusPaysApplicability → ⊥
unifierReviewApplicabilityAliasIsExact =
  Unifier.unifierAcceptedReviewDoesNotPayApplicability

unifierSemanticPromotionTruthAuthorityAliasIsExact :
  Bridge.SemanticPromotionTruthAuthorityClosed
unifierSemanticPromotionTruthAuthorityAliasIsExact =
  Unifier.unifierSemanticPromotionTruthAuthorityClosed

unifierLegalCandidateIsNotAuthority :
  Bridge.CandidateSourceIsAuthoritative → ⊥
unifierLegalCandidateIsNotAuthority =
  Unifier.unifierLegalCandidateSourceDoesNotCloseAuthority

unifierExactReuseAuthorityAliasIsExact :
  Bridge.ExactReuseCreatesSemanticAuthority → ⊥
unifierExactReuseAuthorityAliasIsExact =
  Unifier.unifierExactReuseDoesNotCreateSemanticAuthority
