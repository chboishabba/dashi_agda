module DASHI.Cognition.PNF.SparseFrontierConstraints where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.SparseFibredFrontier

------------------------------------------------------------------------
-- Typed constraints describe the relational evidence required from a bounded
-- candidate actor/factor.  Residual class remains a demand-strategy index and
-- is not falsely treated as a property of the candidate target.
------------------------------------------------------------------------

data ConstraintKind : Set where
  factorTypeConstraint : ConstraintKind
  objectKindConstraint : ConstraintKind
  lexicalConstraint : ConstraintKind
  roleConstraint : ConstraintKind
  definitionConstraint : ConstraintKind
  scopeConstraint : ConstraintKind

data ConstraintPolarity : Set where
  requirePresent forbidPresent : ConstraintPolarity

record TypedFrontierConstraint : Set where
  constructor typedFrontierConstraint
  field
    constraintKind : ConstraintKind
    constraintKeyA constraintKeyB : Nat
    constraintPolarity : ConstraintPolarity

open TypedFrontierConstraint public

------------------------------------------------------------------------
-- One actor identity may have several compressed action summaries.  Evidence
-- for a conjunction may therefore be distributed across that profile family
-- without reopening the actor's child proposition graph.
------------------------------------------------------------------------

record ActorProfileFamily : Set where
  constructor actorProfileFamily
  field
    familyActorIdentity : Nat
    familyProfileCount : Nat

open ActorProfileFamily public

record ConstraintEvidence
  (family : ActorProfileFamily)
  (constraint : TypedFrontierConstraint) : Set where
  constructor constraintEvidence
  field
    witnessProfileOrdinal : Nat
    witnessOrdinalIsBounded :
      witnessProfileOrdinal ≤ᶜ familyProfileCount family

open ConstraintEvidence public

data ConstraintVerdict
  (family : ActorProfileFamily)
  (constraint : TypedFrontierConstraint) : Set where
  requiredWitness :
    constraintPolarity constraint ≡ requirePresent →
    ConstraintEvidence family constraint →
    ConstraintVerdict family constraint
  forbiddenAbsence :
    constraintPolarity constraint ≡ forbidPresent →
    (ConstraintEvidence family constraint → ⊥) →
    ConstraintVerdict family constraint

------------------------------------------------------------------------
-- A local chain models conjunction.  Every required-positive constraint needs
-- evidence and every required-negative constraint needs evidence absence.
------------------------------------------------------------------------

data ConstraintChain : Set where
  noConstraints : ConstraintChain
  _then_ : TypedFrontierConstraint → ConstraintChain → ConstraintChain

infixr 5 _then_

data SatisfiesConstraintChain
  (family : ActorProfileFamily) : ConstraintChain → Set where
  satisfiesNoConstraints :
    SatisfiesConstraintChain family noConstraints
  satisfiesNextConstraint :
    ∀ {constraint rest} →
    ConstraintVerdict family constraint →
    SatisfiesConstraintChain family rest →
    SatisfiesConstraintChain family (constraint then rest)

------------------------------------------------------------------------
-- Filtering authority is restricted to an already bounded candidate relation.
-- There is deliberately no constructor authorising a global object inventory
-- scan to satisfy a local typed hole.
------------------------------------------------------------------------

data CandidateCarrier : Set where
  boundedFrontierCandidates : CandidateCarrier
  globalDocumentInventory : CandidateCarrier

data ConstraintFilteringPermission : CandidateCarrier → Set where
  filterBoundedFrontierCandidates :
    ConstraintFilteringPermission boundedFrontierCandidates

globalInventoryCannotFilterTypedHole :
  ConstraintFilteringPermission globalDocumentInventory → ⊥
globalInventoryCannotFilterTypedHole ()

record BoundedCandidateSet : Set where
  constructor boundedCandidateSet
  field
    candidateCount candidateLimit : Nat
    candidatesRespectLimit : candidateCount ≤ᶜ candidateLimit

open BoundedCandidateSet public

record AdmittedConstrainedCandidate
  (family : ActorProfileFamily)
  (constraints : ConstraintChain) : Set where
  constructor admittedConstrainedCandidate
  field
    boundedCandidates : BoundedCandidateSet
    filteringPermission :
      ConstraintFilteringPermission boundedFrontierCandidates
    satisfiesAllConstraints :
      SatisfiesConstraintChain family constraints

open AdmittedConstrainedCandidate public

record SparseConstraintBoundary : Set where
  constructor sparseConstraintBoundary
  field
    globalInventoryHasNoPermission :
      ConstraintFilteringPermission globalDocumentInventory → ⊥
    boundedCandidatePermission :
      ConstraintFilteringPermission boundedFrontierCandidates

open SparseConstraintBoundary public

canonicalSparseConstraintBoundary : SparseConstraintBoundary
canonicalSparseConstraintBoundary =
  sparseConstraintBoundary
    globalInventoryCannotFilterTypedHole
    filterBoundedFrontierCandidates
