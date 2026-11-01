module DASHI.Cognition.PNF.IndexedSparseFrontierActorRetentionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Concrete actor-retention semantics for SensibLaw migration 179.
--
-- Migration 062 preserves a low-salience actor profile when any unresolved
-- child object demand can request it through three nullable constraints:
-- factor type, object kind, and role.  Lexical identity is intentionally not
-- part of this retention predicate.  Migration 179 changes only the physical
-- realization from correlated demand scans to indexed key intersection.
------------------------------------------------------------------------

data OptionalEquals : Maybe Nat → Nat → Set where
  wildcardEquals :
    ∀ {actual} → OptionalEquals nothing actual
  requiredEquals :
    ∀ {required actual} →
    required ≡ actual →
    OptionalEquals (just required) actual

record ActorRetentionDemand : Set where
  constructor actorRetentionDemand
  field
    expectedFactorType : Maybe Nat
    expectedObjectKind : Maybe Nat
    expectedRole : Maybe Nat

open ActorRetentionDemand public

record RetainedActorProfile : Set where
  constructor retainedActorProfile
  field
    profileFactorType : Nat
    profileObjectKind : Nat
    profileRole : Nat

open RetainedActorProfile public

record ActorRetentionConstraintWitness
  (demand : ActorRetentionDemand)
  (profile : RetainedActorProfile) : Set where
  constructor actorRetentionConstraintWitness
  field
    factorTypeSatisfied :
      OptionalEquals
        (expectedFactorType demand)
        (profileFactorType profile)
    objectKindSatisfied :
      OptionalEquals
        (expectedObjectKind demand)
        (profileObjectKind profile)
    roleSatisfied :
      OptionalEquals
        (expectedRole demand)
        (profileRole profile)

open ActorRetentionConstraintWitness public

record LegacyActorRetention
  (demand : ActorRetentionDemand)
  (profile : RetainedActorProfile) : Set where
  constructor legacyActorRetention
  field
    legacyRetentionWitness :
      ActorRetentionConstraintWitness demand profile

open LegacyActorRetention public

record IndexedActorRetention
  (demand : ActorRetentionDemand)
  (profile : RetainedActorProfile) : Set where
  constructor indexedActorRetention
  field
    indexedRetentionWitness :
      ActorRetentionConstraintWitness demand profile

open IndexedActorRetention public

legacyToIndexed :
  ∀ {demand profile} →
  LegacyActorRetention demand profile →
  IndexedActorRetention demand profile
legacyToIndexed (legacyActorRetention witness) =
  indexedActorRetention witness

indexedToLegacy :
  ∀ {demand profile} →
  IndexedActorRetention demand profile →
  LegacyActorRetention demand profile
indexedToLegacy (indexedActorRetention witness) =
  legacyActorRetention witness

legacyIndexedRoundTrip :
  ∀ {demand profile}
    (retention : LegacyActorRetention demand profile) →
  indexedToLegacy (legacyToIndexed retention) ≡ retention
legacyIndexedRoundTrip (legacyActorRetention witness) = refl

indexedLegacyRoundTrip :
  ∀ {demand profile}
    (retention : IndexedActorRetention demand profile) →
  legacyToIndexed (indexedToLegacy retention) ≡ retention
indexedLegacyRoundTrip (indexedActorRetention witness) = refl

------------------------------------------------------------------------
-- Wildcard preservation.
------------------------------------------------------------------------

allWildcardRetentionDemand : ActorRetentionDemand
allWildcardRetentionDemand =
  actorRetentionDemand nothing nothing nothing

allWildcardRetentionMatchesEveryProfile :
  (profile : RetainedActorProfile) →
  IndexedActorRetention allWildcardRetentionDemand profile
allWildcardRetentionMatchesEveryProfile profile =
  indexedActorRetention
    (actorRetentionConstraintWitness
      wildcardEquals
      wildcardEquals
      wildcardEquals)
