module DASHI.Physics.SignatureElimination where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _,_)

record OrbitProfile : Set₁ where
  field
    profile : Set

record SignatureCandidate : Set₁ where
  field
    sig : Set

record SignatureAxioms : Set₁ where
  field
    coneCompat    : Set
    arrowCompat   : Set
    isotropyCompat : Set

record EliminatesAllBut31 : Set₁ where
  field
    theorem :
      (OP : OrbitProfile) →
      (Ax : SignatureAxioms) →
      Σ SignatureCandidate (λ s → Set)
