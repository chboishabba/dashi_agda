module DASHI.Physics.Closure.NSTriadKNFiniteSpectralDoesNotImplyUniform where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

------------------------------------------------------------------------
-- Logical obstruction: one exact certificate at every fixed cutoff does not
-- by itself supply a cutoff-independent constant.
------------------------------------------------------------------------

notSuccessor≤Self : ∀ {n} → suc n ≤ n → ⊥
notSuccessor≤Self {zero} ()
notSuccessor≤Self {suc n} (s≤s proof) =
  notSuccessor≤Self proof

EachCutoffHasSomeBound : Set
EachCutoffHasSomeBound =
  (N : Nat) → Σ Nat (λ bound → N ≤ bound)

eachCutoffHasItsOwnExactBound : EachCutoffHasSomeBound
eachCutoffHasItsOwnExactBound N = N , reflexive N
  where
  reflexive : ∀ n → n ≤ n
  reflexive zero = z≤n
  reflexive (suc n) = s≤s (reflexive n)

OneUniformBound : Set
OneUniformBound =
  Σ Nat (λ bound → (N : Nat) → N ≤ bound)

noUniformBoundForIdentityGrowth : OneUniformBound → ⊥
noUniformBoundForIdentityGrowth (bound , uniform) =
  notSuccessor≤Self (uniform (suc bound))

record FixedCutoffSpectralEvidence : Set₁ where
  field
    finiteBoundAt : Nat → Nat
    finiteBoundCertified : (N : Nat) → N ≤ finiteBoundAt N

open FixedCutoffSpectralEvidence public

identityGrowthFiniteEvidence : FixedCutoffSpectralEvidence
identityGrowthFiniteEvidence = record
  { finiteBoundAt = λ N → N
  ; finiteBoundCertified = reflexive
  }
  where
  reflexive : ∀ n → n ≤ n
  reflexive zero = z≤n
  reflexive (suc n) = s≤s (reflexive n)

finiteCertificatesDoNotConstructUniformConstant :
  FixedCutoffSpectralEvidence →
  Set
finiteCertificatesDoNotConstructUniformConstant evidence =
  Σ Nat (λ bound →
    (N : Nat) → finiteBoundAt evidence N ≤ bound)

identityGrowthHasNoUniformConstant :
  finiteCertificatesDoNotConstructUniformConstant
    identityGrowthFiniteEvidence →
  ⊥
identityGrowthHasNoUniformConstant (bound , uniform) =
  notSuccessor≤Self (uniform (suc bound))

finiteToUniformNonImplicationImplemented : Bool
finiteToUniformNonImplicationImplemented = true

finiteToUniformNonImplicationImplementedIsTrue :
  finiteToUniformNonImplicationImplemented ≡ true
finiteToUniformNonImplicationImplementedIsTrue = refl
