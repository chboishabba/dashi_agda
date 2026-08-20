module DASHI.Core.TypedEvidenceDependencyExact where

------------------------------------------------------------------------
-- TYPED EVIDENCE DEPENDENCY
--
-- Cross-domain lesson from Animalexic, SeaMeInIt and LES:
--
--   multiple downstream measurements/receipts derived from one source episode
--   are not automatically multiple independent confirmations;
--
--   changing an upstream artifact reopens exactly those downstream claims for
--   which a dependency path is actually carried.
--
-- The module is deliberately structural.  Statistical independence requires a
-- domain model; this file proves only provenance-root separation and exact
-- dependency reachability.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Evidence episodes / provenance roots.
------------------------------------------------------------------------

record EvidenceItem (Root Payload : Set) : Set where
  constructor evidenceItem
  field
    root : Root
    payload : Payload

open EvidenceItem public

record ProvenanceIndependent
    {Root Payload : Set}
    (left right : EvidenceItem Root Payload) : Set where
  constructor provenanceIndependent
  field
    rootsDistinct : root left ≢ root right

open ProvenanceIndependent public

sameRootContradictsProvenanceIndependence :
  ∀ {Root Payload}
    {left right : EvidenceItem Root Payload} →
  root left ≡ root right →
  ProvenanceIndependent left right →
  ⊥
sameRootContradictsProvenanceIndependence same independent =
  rootsDistinct independent same

------------------------------------------------------------------------
-- Exact dependency closure.  This is the provenance/build-system relation;
-- covariance, correlation, or statistical influence does not construct it.
------------------------------------------------------------------------

data DependencyPath
    {Artifact : Set}
    (DirectlyDependsOn : Artifact → Artifact → Set) :
    Artifact → Artifact → Set where
  direct :
    ∀ {upstream downstream} →
    DirectlyDependsOn upstream downstream →
    DependencyPath DirectlyDependsOn upstream downstream
  extend :
    ∀ {upstream middle downstream} →
    DependencyPath DirectlyDependsOn upstream middle →
    DirectlyDependsOn middle downstream →
    DependencyPath DirectlyDependsOn upstream downstream

appendDependencyPath :
  ∀ {Artifact}
    {DirectlyDependsOn : Artifact → Artifact → Set}
    {left middle right : Artifact} →
  DependencyPath DirectlyDependsOn left middle →
  DependencyPath DirectlyDependsOn middle right →
  DependencyPath DirectlyDependsOn left right
appendDependencyPath first (direct edge) = extend first edge
appendDependencyPath first (extend rest edge) =
  extend (appendDependencyPath first rest) edge

record ChangeInvalidates
    {Artifact : Set}
    (DirectlyDependsOn : Artifact → Artifact → Set)
    (changed derived : Artifact) : Set where
  constructor changeInvalidates
  field
    dependencyPath : DependencyPath DirectlyDependsOn changed derived

open ChangeInvalidates public

invalidationIsTransitive :
  ∀ {Artifact}
    {DirectlyDependsOn : Artifact → Artifact → Set}
    {changed middle derived : Artifact} →
  ChangeInvalidates DirectlyDependsOn changed middle →
  ChangeInvalidates DirectlyDependsOn middle derived →
  ChangeInvalidates DirectlyDependsOn changed derived
invalidationIsTransitive left right =
  changeInvalidates
    (appendDependencyPath
      (dependencyPath left)
      (dependencyPath right))

------------------------------------------------------------------------
-- Reopenability reasons are typed because their triggers differ.
------------------------------------------------------------------------

data ReopenReason : Set where
  budgetDeferred : ReopenReason
  ambiguityUnresolved : ReopenReason
  dependencyChanged : ReopenReason
  fidelityEscalation : ReopenReason
  policyChanged : ReopenReason

data AlternativeStatus : Set where
  active : AlternativeStatus
  reopenable : ReopenReason → AlternativeStatus
  refuted : AlternativeStatus

record ReopeningTrigger (Trigger : Set) : Set₁ where
  constructor reopeningTrigger
  field
    triggerFor : ReopenReason → Trigger → Set

open ReopeningTrigger public

record ReopenableAlternative (Payload Trigger : Set) : Set₁ where
  constructor reopenableAlternative
  field
    payload : Payload
    status : AlternativeStatus
    TriggerMatches : Trigger → Set

open ReopenableAlternative public

------------------------------------------------------------------------
-- Boundary: provenance separation is a necessary structural distinction, not a
-- proof of probabilistic independence; exact dependency reachability is not
-- inferred from model covariance.
------------------------------------------------------------------------
