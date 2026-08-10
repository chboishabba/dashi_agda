module DASHI.Cognition.PNF.ProofRelevantFactorDerivations where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority
open import DASHI.Cognition.PNF.ProofRelevantIdentityFibres

------------------------------------------------------------------------
-- Immutable local factors remain premises.  Identity substitution creates a
-- separate derived proposition carrying its proof witness; it never mutates or
-- replaces the premise factor.
------------------------------------------------------------------------

data DerivationKind : Set where
  identitySubstitution factorComposition : DerivationKind

data DerivationState : Set where
  derivationCandidate derivationAdmitted derivationRejected derivationSuperseded :
    DerivationState

record IdentitySubstitutionProof : Set where
  constructor identitySubstitutionProof
  field
    substitutionPremiseFactor : FactorId
    substitutionSourceObject : ObjectId
    substitutionTargetEntity : CanonicalEntity
    substitutionWitness : AdmittedIdentityWitness

open IdentitySubstitutionProof public

record WitnessedDerivedArgument : Set where
  constructor witnessedDerivedArgument
  field
    derivedArgumentRole : Nat
    derivedArgumentSourceObject : ObjectId
    derivedArgumentEntity : CanonicalEntity
    derivedArgumentProof : AdmittedIdentityWitness

open WitnessedDerivedArgument public

record IdentitySubstitutionDerivation : Set where
  constructor identitySubstitutionDerivation
  field
    substitutionProof : IdentitySubstitutionProof
    premiseRetained : FactorId
    premiseMatchesProof :
      premiseRetained ≡ substitutionPremiseFactor substitutionProof
    substitutedArgument : WitnessedDerivedArgument

open IdentitySubstitutionDerivation public

------------------------------------------------------------------------
-- Shared objects or shared admitted entity fibres establish only structural
-- composability.  A composition candidate has no constructor for semantic
-- proposition admission.  An explicit domain rule is a separate authority.
------------------------------------------------------------------------

data CompositionBridge : Set where
  localObjectBridge : ObjectId → CompositionBridge
  witnessedEntityBridge : CanonicalEntity → AdmittedIdentityWitness → CompositionBridge

record FactorCompositionCandidate : Set where
  constructor factorCompositionCandidate
  field
    leftPremiseFactor : FactorId
    rightPremiseFactor : FactorId
    leftBridgeRole rightBridgeRole : Nat
    bridge : CompositionBridge
    candidateRank candidateLimit : Nat

open FactorCompositionCandidate public

data CompositionAuthority : Set where
  candidateOnlyAuthority : CompositionAuthority
  explicitDomainRuleAuthority : CompositionAuthority

data CompositionPermission : CompositionAuthority → Set where
  explicitDomainRuleMayCompose :
    CompositionPermission explicitDomainRuleAuthority

candidateAloneCannotDeriveProposition :
  CompositionPermission candidateOnlyAuthority → ⊥
candidateAloneCannotDeriveProposition ()

record AdmittedFactorComposition : Set where
  constructor admittedFactorComposition
  field
    compositionCandidate : FactorCompositionCandidate
    compositionPermission :
      CompositionPermission explicitDomainRuleAuthority
    compositionRuleIdentity : Nat

open AdmittedFactorComposition public

------------------------------------------------------------------------
-- A proposition has exactly one admitted derivation constructor per currently
-- implemented semantic path.  The factor-composition constructor requires the
-- explicit rule-bearing record above; a candidate by itself is not enough.
------------------------------------------------------------------------

data DerivedProposition : DerivationKind → Set where
  propositionByIdentitySubstitution :
    IdentitySubstitutionDerivation →
    DerivedProposition identitySubstitution
  propositionByAdmittedComposition :
    AdmittedFactorComposition →
    DerivedProposition factorComposition

record FactorDerivationBoundary : Set where
  constructor factorDerivationBoundary
  field
    candidateHasNoCompositionPermission :
      CompositionPermission candidateOnlyAuthority → ⊥
    explicitRuleCanCompose :
      CompositionPermission explicitDomainRuleAuthority

open FactorDerivationBoundary public

canonicalFactorDerivationBoundary : FactorDerivationBoundary
canonicalFactorDerivationBoundary =
  factorDerivationBoundary
    candidateAloneCannotDeriveProposition
    explicitDomainRuleMayCompose
