module DASHI.Core.ThresholdCSPCores where

open import DASHI.Core.Prelude
open import DASHI.Core.NonlinearExplodedSparsity

Predicate : Set → Set₁
Predicate X = X → Set

Subset : {X : Set} → Predicate X → Predicate X → Set
Subset {X} P Q = (x : X) → P x → Q x

ProperSubset : {X : Set} → Predicate X → Predicate X → Set
ProperSubset P Q = Subset P Q × ¬ Subset Q P

RestrictedSatisfiable :
  {X L : Set} → ThresholdKernel X L → Predicate X → Set₁
RestrictedSatisfiable {X} K Clauses =
  Σ (State X) (λ s → (x : X) → Clauses x → LocalConstraint K s x)

RestrictedUnsatisfiable :
  {X L : Set} → ThresholdKernel X L → Predicate X → Set₁
RestrictedUnsatisfiable K Clauses = ¬ RestrictedSatisfiable K Clauses

record MinimalInconsistentCore
  {X L : Set}
  (K : ThresholdKernel X L)
  (Core : Predicate X) : Set₁ where
  field
    inconsistent : RestrictedUnsatisfiable K Core
    everyProperRestrictionConsistent :
      (Sub : Predicate X) → ProperSubset Sub Core →
      RestrictedSatisfiable K Sub

open MinimalInconsistentCore public

RemainingAfterRemoval :
  {X : Set} → Predicate X → Predicate X → Predicate X
RemainingAfterRemoval Clauses Removed x = Clauses x × ¬ Removed x

record RemovalRestores
  {X L : Set}
  (K : ThresholdKernel X L)
  (Clauses Removed : Predicate X) : Set₁ where
  field
    restored : RestrictedSatisfiable K (RemainingAfterRemoval Clauses Removed)

record Intersects
  {X : Set}
  (Removed Core : Predicate X) : Set₁ where
  field
    witness : X
    removedWitness : Removed witness
    coreWitness : Core witness

record CoreRepairSet
  {X : Set}
  (Family : Predicate X → Set)
  (Removed : Predicate X) : Set₁ where
  field
    intersectsEveryCore :
      (Core : Predicate X) → Family Core → Intersects Removed Core

DefectSupport :
  {X L : Set} → ThresholdKernel X L → State X → Predicate X
DefectSupport K s = KernelDefect K s

record DefectCoreCertificate
  {X L : Set}
  (K : ThresholdKernel X L)
  (s : State X)
  (Core : Predicate X) : Set₁ where
  field
    containedInObservedDefect : Subset Core (DefectSupport K s)
    minimalInconsistent : MinimalInconsistentCore K Core

open DefectCoreCertificate public

minimalCoreIsInconsistent :
  {X L : Set} {K : ThresholdKernel X L} {Core : Predicate X} →
  MinimalInconsistentCore K Core → RestrictedUnsatisfiable K Core
minimalCoreIsInconsistent = inconsistent

properSubcoreRestoresConsistency :
  {X L : Set} {K : ThresholdKernel X L} {Core : Predicate X} →
  (M : MinimalInconsistentCore K Core) →
  (Sub : Predicate X) → ProperSubset Sub Core →
  RestrictedSatisfiable K Sub
properSubcoreRestoresConsistency M = everyProperRestrictionConsistent M

-- An observed KernelDefect is only a violated local clause for one state.
-- Minimal-core status requires a separate DefectCoreCertificate.
