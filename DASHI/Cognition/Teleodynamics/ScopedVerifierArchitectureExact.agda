module DASHI.Cognition.Teleodynamics.ScopedVerifierArchitectureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.LLMWeightedFutureQuotientExact
import DASHI.Cognition.PNF.LLMContextWindowTerminalisationExact
import DASHI.Cognition.PNF.LLMResidualHierarchyExact
import DASHI.Cognition.PNF.NeuralProposalEvidenceBoundaryExact
import DASHI.Cognition.Teleodynamics.TeleodynamicSemanticActionBridgeExact

data VerificationStatus : Set where
  verified refuted unresolved outOfDomain : VerificationStatus

record ScopedValidator (X : Set) : Set₁ where
  constructor scoped-validator
  field
    Applicable : X → Set
    Claim : X → Set
    Certificate : X → Set
    status : X → VerificationStatus
    accepts : (x : X) → status x ≡ verified → Certificate x
    sound : (x : X) → Applicable x → status x ≡ verified → Claim x
open ScopedValidator public

record ValidationReceipt {X : Set} (V : ScopedValidator X) (x : X) : Set where
  constructor validation-receipt
  field
    applicable : Applicable V x
    verifiedStatus : status V x ≡ verified
    certificate : Certificate V x
    claimPaid : Claim V x
open ValidationReceipt public

receiptFromVerified : ∀ {X : Set} (V : ScopedValidator X) (x : X) → Applicable V x → status V x ≡ verified → ValidationReceipt V x
receiptFromVerified V x app eq = validation-receipt app eq (accepts V x eq) (sound V x app eq)

record PairValidationReceipt {X : Set} (V₁ V₂ : ScopedValidator X) (x : X) : Set where
  constructor pair-validation-receipt
  field
    left : ValidationReceipt V₁ x
    right : ValidationReceipt V₂ x
open PairValidationReceipt public

pairClaimsPaid : ∀ {X : Set} {V₁ V₂ : ScopedValidator X} {x : X} → PairValidationReceipt V₁ V₂ x → Claim V₁ x × Claim V₂ x
pairClaimsPaid r = claimPaid (left r) , claimPaid (right r)

data UniversalTruthOracleFromScopedValidator : Set where
data OutOfDomainCreatesVerification : Set where
data UnresolvedCreatesVerification : Set where

noUniversalTruthOracleFromScopedValidator : UniversalTruthOracleFromScopedValidator → ⊥
noUniversalTruthOracleFromScopedValidator ()
outOfDomainDoesNotCreateVerification : OutOfDomainCreatesVerification → ⊥
outOfDomainDoesNotCreateVerification ()
unresolvedDoesNotCreateVerification : UnresolvedCreatesVerification → ⊥
unresolvedDoesNotCreateVerification ()

record ScopedVerifierArchitectureBoundary : Set where
  constructor scoped-verifier-architecture-boundary
  field
    probabilisticProposalAllowed : Bool
    verifierApplicabilityExplicit : Bool
    certificatesExplicit : Bool
    unresolvedStateExplicit : Bool
    outOfDomainStateExplicit : Bool
    verifierCompositionConjunctive : Bool
    universalFalsehoodDetectorClaimed : Bool
    knowledgeGraphCreatesTruth : Bool
    deterministicDecodeCreatesSemanticCorrectness : Bool

canonicalScopedVerifierArchitectureBoundary : ScopedVerifierArchitectureBoundary
canonicalScopedVerifierArchitectureBoundary = scoped-verifier-architecture-boundary true true true true true true false false false
