module DASHI.Cognition.PNF.IndexedSparseFrontierCandidateExposureRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)

open import DASHI.Cognition.PNF.IndexedSparseFrontierCandidateExposureExact

data Demand : Set where
  d₀ d₁ : Demand

data Profile : Set where
  p₀ p₁ p₂ : Profile

candidateRelation : Demand → Profile → Set
candidateRelation d₀ p₀ = ⊤
candidateRelation d₀ p₁ = ⊤
candidateRelation d₀ p₂ = ⊤
candidateRelation d₁ p₀ = ⊤
candidateRelation d₁ p₁ = ⊤
candidateRelation d₁ p₂ = ⊤

exactAuthority : CandidateAuthority Demand Profile
exactAuthority = record
  { candidateWise = candidateRelation
  ; indexedIntersection = candidateRelation
  ; exact = λ demand profile → refl
  }

legacy : ExposureReceipt
legacy = candidateWiseReceipt 2 3 4 7 6

indexed : ExposureReceipt
indexed = indexedReceipt 2 3 4 7 5 6

exactReduction : ExactIndexedSparseFrontierReduction Demand Profile
exactReduction = record
  { authority = exactAuthority
  ; legacyReceipt = legacy
  ; indexedReceiptWitness = indexed
  ; sameDemandPopulation = refl
  ; sameProfilePopulation = refl
  ; sameCandidateAuthorityCount = refl
  }

candidateAuthorityPreserved :
  candidateWise exactAuthority d₀ p₁
    ≡ indexedIntersection exactAuthority d₀ p₁
candidateAuthorityPreserved = sameCandidateRelation exactReduction d₀ p₁

wildcardConstraintPreserved :
  KeyIntersectionWitness
    (requiredKeyFamily 0)
    (profileKeyFamily 5)
wildcardConstraintPreserved =
  emptyRequiredKeysAreSatisfied (profileKeyFamily 5)

transitionReceipt : SparseFrontierTransitionCertificate
transitionReceipt =
  sparseFrontierTransitionCertificate
    10
    2
    3
    4
    7
    5
    6
    16
    refl
