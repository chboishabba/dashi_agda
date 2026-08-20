module DASHI.Core.TypedEvidenceDependencyExact where

------------------------------------------------------------------------
-- TYPED EVIDENCE DEPENDENCY
--
-- Cross-domain lesson from Animalexic, SeaMeInIt and LES:
-- multiple downstream measurements/receipts derived from one source episode
-- are not automatically multiple independent confirmations.  Exact reopening
-- reuses AffectedDependencyClosureExact rather than defining another closure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.AffectedDependencyClosureExact as Affected

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

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
-- Canonical dependency/reopening aliases.  Covariance or statistical influence
-- does not construct these paths; the upstream module owns that boundary.
------------------------------------------------------------------------

DependencyPath :
  ∀ {Artifact : Set} →
  (Artifact → Artifact → Set) → Artifact → Artifact → Set
DependencyPath = Affected.AffectedClosure

ChangeInvalidates :
  ∀ {Artifact : Set} →
  (Artifact → Artifact → Set) → Artifact → Artifact → Set
ChangeInvalidates = Affected.ReopeningObligation

invalidationIsTransitive :
  ∀ {Artifact}
    {DirectlyDependsOn : Artifact → Artifact → Set}
    {changed middle derived : Artifact} →
  ChangeInvalidates DirectlyDependsOn changed middle →
  ChangeInvalidates DirectlyDependsOn middle derived →
  ChangeInvalidates DirectlyDependsOn changed derived
invalidationIsTransitive = Affected.obligationsCompose

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
-- Boundary: provenance-root separation is structural evidence, not a proof of
-- probabilistic independence.  Exact dependency reachability remains the
-- canonical AffectedDependencyClosureExact theorem surface.
------------------------------------------------------------------------
