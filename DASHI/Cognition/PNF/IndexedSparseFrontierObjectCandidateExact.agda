module DASHI.Cognition.PNF.IndexedSparseFrontierObjectCandidateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Concrete object-candidate semantics for SensibLaw migration 178.
--
-- Migration 062's historical object_candidate relation admits an actor profile
-- when four nullable constraints hold:
--   * expected factor type = profile factor type, when present;
--   * expected object kind = profile object kind, when present;
--   * role = profile role, when present;
--   * lexical key = object head OR profile predicate, when present.
--
-- The indexed implementation may change candidate exposure, but it must not
-- change these semantics.  In particular, an absent constraint is wildcard
-- evidence, not negative evidence.
------------------------------------------------------------------------

data OptionalEquals : Maybe Nat → Nat → Set where
  wildcardEquals :
    ∀ {actual} → OptionalEquals nothing actual
  requiredEquals :
    ∀ {required actual} →
    required ≡ actual →
    OptionalEquals (just required) actual

-- Lexical identity is deliberately disjunctive: the old SQL accepted either
-- the represented object's head symbol or the profile predicate symbol.
data OptionalLexicalMatch : Maybe Nat → Nat → Nat → Set where
  wildcardLexical :
    ∀ {head predicate} →
    OptionalLexicalMatch nothing head predicate
  lexicalMatchesHead :
    ∀ {required head predicate} →
    required ≡ head →
    OptionalLexicalMatch (just required) head predicate
  lexicalMatchesPredicate :
    ∀ {required head predicate} →
    required ≡ predicate →
    OptionalLexicalMatch (just required) head predicate

record ObjectDemandKeys : Set where
  constructor objectDemandKeys
  field
    expectedFactorType : Maybe Nat
    expectedObjectKind : Maybe Nat
    expectedLexical : Maybe Nat
    expectedRole : Maybe Nat

open ObjectDemandKeys public

record ActorProfileKeys : Set where
  constructor actorProfileKeys
  field
    profileFactorType : Nat
    profileObjectKind : Nat
    profileHeadSymbol : Nat
    profilePredicateSymbol : Nat
    profileRole : Nat

open ActorProfileKeys public

-- This is the semantic conjunction shared by the legacy Cartesian filter and
-- the indexed key-intersection implementation.
record ObjectCandidateConstraintWitness
  (demand : ObjectDemandKeys)
  (profile : ActorProfileKeys) : Set where
  constructor objectCandidateConstraintWitness
  field
    factorTypeSatisfied :
      OptionalEquals
        (expectedFactorType demand)
        (profileFactorType profile)
    objectKindSatisfied :
      OptionalEquals
        (expectedObjectKind demand)
        (profileObjectKind profile)
    lexicalSatisfied :
      OptionalLexicalMatch
        (expectedLexical demand)
        (profileHeadSymbol profile)
        (profilePredicateSymbol profile)
    roleSatisfied :
      OptionalEquals
        (expectedRole demand)
        (profileRole profile)

open ObjectCandidateConstraintWitness public

-- Two physical realizations intentionally wrap the same semantic witness.  The
-- distinction represents execution strategy only: legacy code obtains the
-- witness by demand × profile exposure and filtering; indexed code obtains it
-- by typed-key intersection.
record LegacyObjectCandidate
  (demand : ObjectDemandKeys)
  (profile : ActorProfileKeys) : Set where
  constructor legacyObjectCandidate
  field
    legacyConstraintWitness :
      ObjectCandidateConstraintWitness demand profile

open LegacyObjectCandidate public

record IndexedObjectCandidate
  (demand : ObjectDemandKeys)
  (profile : ActorProfileKeys) : Set where
  constructor indexedObjectCandidate
  field
    indexedConstraintWitness :
      ObjectCandidateConstraintWitness demand profile

open IndexedObjectCandidate public

legacyToIndexed :
  ∀ {demand profile} →
  LegacyObjectCandidate demand profile →
  IndexedObjectCandidate demand profile
legacyToIndexed (legacyObjectCandidate witness) =
  indexedObjectCandidate witness

indexedToLegacy :
  ∀ {demand profile} →
  IndexedObjectCandidate demand profile →
  LegacyObjectCandidate demand profile
indexedToLegacy (indexedObjectCandidate witness) =
  legacyObjectCandidate witness

legacyIndexedRoundTrip :
  ∀ {demand profile}
    (candidate : LegacyObjectCandidate demand profile) →
  indexedToLegacy (legacyToIndexed candidate) ≡ candidate
legacyIndexedRoundTrip (legacyObjectCandidate witness) = refl

indexedLegacyRoundTrip :
  ∀ {demand profile}
    (candidate : IndexedObjectCandidate demand profile) →
  legacyToIndexed (indexedToLegacy candidate) ≡ candidate
indexedLegacyRoundTrip (indexedObjectCandidate witness) = refl

------------------------------------------------------------------------
-- Explicit wildcard witness used by the runtime's broad fallback.
------------------------------------------------------------------------

allWildcardDemand : ObjectDemandKeys
allWildcardDemand =
  objectDemandKeys nothing nothing nothing nothing

allWildcardMatchesEveryProfile :
  (profile : ActorProfileKeys) →
  IndexedObjectCandidate allWildcardDemand profile
allWildcardMatchesEveryProfile profile =
  indexedObjectCandidate
    (objectCandidateConstraintWitness
      wildcardEquals
      wildcardEquals
      wildcardLexical
      wildcardEquals)
