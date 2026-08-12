module DASHI.Crypto.PublicSecretFactorisationAttackExact where

------------------------------------------------------------------------
-- PUBLIC FACTORISATION ATTACKS
--
-- A KEM can fail without reconstructing every hidden variable.  The decisive
-- question is whether the protected secret-label map factors through public
-- observations.  This module formalises an exact, probability-free attack
-- hierarchy.  Computational feasibility is intentionally a separate layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

record SecretLabelledProjection : Set₁ where
  constructor secretLabelledProjection
  field
    Fine Public Secret : Set
    project : Fine → Public
    secretLabel : Fine → Secret

open SecretLabelledProjection public

------------------------------------------------------------------------
-- Exact public recovery of the protected secret label.
------------------------------------------------------------------------

record ExactPublicSecretRecovery
    (system : SecretLabelledProjection) : Set₁ where
  constructor exactPublicSecretRecovery
  field
    recover : Public system → Secret system
    factors : ∀ fine → recover (project system fine) ≡ secretLabel system fine

open ExactPublicSecretRecovery public

------------------------------------------------------------------------
-- Full inversion is strictly stronger than needed for a KEM break at this
-- abstraction level.  Full inversion implies secret recovery by composition.
------------------------------------------------------------------------

record FullPublicInversion
    (system : SecretLabelledProjection) : Set₁ where
  constructor fullPublicInversion
  field
    invert : Public system → Fine system
    inverseOnImage : ∀ fine → invert (project system fine) ≡ fine

open FullPublicInversion public

fullInversionImpliesSecretRecovery :
  ∀ {system} →
  FullPublicInversion system →
  ExactPublicSecretRecovery system
fullInversionImpliesSecretRecovery {system} inversion =
  exactPublicSecretRecovery
    (λ public → secretLabel system (invert inversion public))
    (λ fine → cong (secretLabel system) (inverseOnImage inversion fine))

------------------------------------------------------------------------
-- Partial leakage can be weaker than exact key recovery.  A protected Boolean
-- predicate of the secret may already factor through the public observation.
------------------------------------------------------------------------

record PublicPredicateLeak
    (system : SecretLabelledProjection)
    (predicate : Secret system → Bool) : Set₁ where
  constructor publicPredicateLeak
  field
    observe : Public system → Bool
    leaks : ∀ fine →
      observe (project system fine) ≡ predicate (secretLabel system fine)

open PublicPredicateLeak public

exactRecoveryLeaksEveryPredicate :
  ∀ {system}
    (recovery : ExactPublicSecretRecovery system)
    (predicate : Secret system → Bool) →
  PublicPredicateLeak system predicate
exactRecoveryLeaksEveryPredicate {system} recovery predicate =
  publicPredicateLeak
    (λ public → predicate (recover recovery public))
    (λ fine → cong predicate (factors recovery fine))

------------------------------------------------------------------------
-- A factorisation may pass through any smaller/intermediate quotient Z.  This
-- is the exact formal version of "the attacker need not invert the lattice;
-- it is enough to find a public invariant that determines the shared secret".
------------------------------------------------------------------------

record PublicSecretFactorisation
    (system : SecretLabelledProjection) : Set₁ where
  constructor publicSecretFactorisation
  field
    Intermediate : Set
    quotient : Public system → Intermediate
    decode : Intermediate → Secret system
    factorLaw : ∀ fine →
      decode (quotient (project system fine)) ≡ secretLabel system fine

open PublicSecretFactorisation public

factorisationImpliesExactRecovery :
  ∀ {system} →
  PublicSecretFactorisation system →
  ExactPublicSecretRecovery system
factorisationImpliesExactRecovery factorisation =
  exactPublicSecretRecovery
    (λ public → decode factorisation (quotient factorisation public))
    (factorLaw factorisation)

------------------------------------------------------------------------
-- Boundary: exact public recovery is already a break of the secret-labelled
-- asymmetry even when the complete fine state remains unknown.
------------------------------------------------------------------------

record SecretAsymmetryBoundary
    (system : SecretLabelledProjection) : Set₁ where
  constructor secretAsymmetryBoundary
  field
    exactPublicRecoveryForbidden : ExactPublicSecretRecovery system → ⊥

open SecretAsymmetryBoundary public
