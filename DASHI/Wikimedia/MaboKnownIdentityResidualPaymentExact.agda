module DASHI.Wikimedia.MaboKnownIdentityResidualPaymentExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboReviewedEvidencePaymentExact as Evidence
import DASHI.Wikimedia.MaboDurableIdentityBaselineExact as Baseline

------------------------------------------------------------------------
-- A durably known identity may pay an open residual without advancing novelty.
-- This is the restart-safe complement of discovery admission.
------------------------------------------------------------------------

record KnownIdentityResidualPayment : Set where
  constructor known-identity-residual-payment
  field
    identityClassReference : String
    triggeringResidualReference : String
    reviewedEvidenceReference : String
    observedResidualContraction : Nat
    closesResidualCandidate : Bool
    closesResidualCandidateIsTrue : closesResidualCandidate ≡ true
    advancesNovelIdentityCardinality : Bool
    advancesNovelIdentityCardinalityIsFalse : advancesNovelIdentityCardinality ≡ false
    createsDiscoveryLineage : Bool
    createsDiscoveryLineageIsFalse : createsDiscoveryLineage ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    promotesApplicability : Bool
    promotesApplicabilityIsFalse : promotesApplicability ≡ false
    promotesClaimTruth : Bool
    promotesClaimTruthIsFalse : promotesClaimTruth ≡ false

open KnownIdentityResidualPayment public

maboEddieKnownIdentityPayment : KnownIdentityResidualPayment
maboEddieKnownIdentityPayment =
  known-identity-residual-payment
    "world-object:eddie-mabo"
    "residual:mabo:participant-identity"
    (Evidence.reviewReference Evidence.maboParticipantIdentityReview)
    1
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

maboKnownIdentityDoesNotAdvanceNovelty :
  advancesNovelIdentityCardinality maboEddieKnownIdentityPayment ≡ false
maboKnownIdentityDoesNotAdvanceNovelty = refl

maboKnownIdentityPaymentContractsResidual :
  observedResidualContraction maboEddieKnownIdentityPayment ≡ 1
maboKnownIdentityPaymentContractsResidual = refl

------------------------------------------------------------------------
-- Persistence transaction boundary.
------------------------------------------------------------------------

record KnownIdentityPaymentCommitBoundary : Set where
  constructor known-identity-payment-commit-boundary
  field
    paymentWorldRecordPersistsBeforeFrontierCommit : Bool
    paymentWorldRecordPersistsBeforeFrontierCommitIsTrue :
      paymentWorldRecordPersistsBeforeFrontierCommit ≡ true
    persistenceFailureMayAdvanceFrontier : Bool
    persistenceFailureMayAdvanceFrontierIsFalse :
      persistenceFailureMayAdvanceFrontier ≡ false
    persistenceFailureMayAdvanceNovelty : Bool
    persistenceFailureMayAdvanceNoveltyIsFalse :
      persistenceFailureMayAdvanceNovelty ≡ false

open KnownIdentityPaymentCommitBoundary public

canonicalKnownIdentityPaymentCommitBoundary : KnownIdentityPaymentCommitBoundary
canonicalKnownIdentityPaymentCommitBoundary =
  known-identity-payment-commit-boundary
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data KnownIdentityPaymentEqualsNovelAdmission : Set where
data KnownIdentityPaymentEqualsDiscoveryLineage : Set where
data PersistedPaymentEqualsClaimTruth : Set where
data PersistedIdentityEqualsAuthority : Set where

data DurableBaselineEqualsOpenResidualPayment : Set where

knownIdentityPaymentDoesNotEqualNovelAdmission :
  KnownIdentityPaymentEqualsNovelAdmission → ⊥
knownIdentityPaymentDoesNotEqualNovelAdmission ()

knownIdentityPaymentDoesNotEqualDiscoveryLineage :
  KnownIdentityPaymentEqualsDiscoveryLineage → ⊥
knownIdentityPaymentDoesNotEqualDiscoveryLineage ()

persistedPaymentDoesNotEqualClaimTruth : PersistedPaymentEqualsClaimTruth → ⊥
persistedPaymentDoesNotEqualClaimTruth ()

persistedIdentityDoesNotEqualAuthority : PersistedIdentityEqualsAuthority → ⊥
persistedIdentityDoesNotEqualAuthority ()

durableBaselineDoesNotEqualOpenResidualPayment :
  DurableBaselineEqualsOpenResidualPayment → ⊥
durableBaselineDoesNotEqualOpenResidualPayment ()
