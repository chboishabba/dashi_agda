module DASHI.Interop.SLRActorCriticPromotionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

record CommitId : Set where
  constructor commitId
  field value : String

record PrincipalId : Set where
  constructor principalId
  field value : String

record ActorCandidate (c : CommitId) : Set where
  constructor actorCandidate
  field actor : PrincipalId

-- The independent check is an explicit trusted-boundary input. A caller
-- must validate principal independence, checker success and digests.
-- Agda cannot authenticate a real external principal or execution.
record IndependentCheck (c : CommitId) : Set where
  constructor independentCheck
  field
    verifier : PrincipalId
    checkDigest : String
    environmentDigest : String
    dependencyDigest : String

record Verified (c : CommitId) : Set where
  constructor independentlyVerified
  field check : IndependentCheck c

verifyWithIndependentCheck : ∀ {c} → IndependentCheck c → Verified c
verifyWithIndependentCheck = independentlyVerified

-- No ActorCandidate -> Verified function is provided. In particular,
-- actorCandidate has no independent-check constructor or certificate.
record ReceiptFor (c : CommitId) : Set where
  constructor receiptFor
  field checked : Verified c

record AuthorizedTransition (c₁ c₂ : CommitId) : Set where
  constructor authorizedTransition
  field
    sourceReceipt : ReceiptFor c₁
    sameCommit : c₁ ≡ c₂

-- An authorization for a different commit requires an impossible equality.
commitBoundNonTransferability : ∀ {c₁ c₂} →
  ReceiptFor c₁ → (c₁ ≡ c₂ → ⊥) →
  AuthorizedTransition c₁ c₂ → ⊥
commitBoundNonTransferability _ unequal transition =
  unequal (AuthorizedTransition.sameCommit transition)

record AllRequiredChecksPassed (c : CommitId) : Set where
  constructor allRequiredChecksPassed
  field
    checkReceipt : ReceiptFor c
    policyGate : IndependentCheck c
    provenanceGate : IndependentCheck c

record MergeEligible (c : CommitId) : Set where
  constructor mergeEligible
  field allChecks : AllRequiredChecksPassed c

mergeGateSoundness : ∀ {c} →
  MergeEligible c → AllRequiredChecksPassed c
mergeGateSoundness = MergeEligible.allChecks

-- Constructive eligibility requires all three independent witness slots.
authorizeMerge : ∀ {c} →
  AllRequiredChecksPassed c → MergeEligible c
authorizeMerge = mergeEligible
