module DASHI.Cognition.PNF.IndexedSparseFrontierTransitionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero)

import DASHI.Cognition.PNF.IndexedSparseFrontierActorRetentionExact as Retention
import DASHI.Cognition.PNF.IndexedSparseFrontierObjectCandidateExact as Candidate

------------------------------------------------------------------------
-- Joint transition certificate for SensibLaw migrations 178/179.
--
-- Sparse parent reduction has two distinct demand/profile relations:
--   1. low-salience actor retention (factor/object-kind/role only), then
--   2. object candidate admission (factor/object-kind/role + lexical head|pred).
--
-- Exactness must hold for both.  Physical exposure is recorded separately so a
-- semantically sparse frontier cannot hide a demand × profile construction.
------------------------------------------------------------------------

record TransitionExposure : Set where
  constructor transitionExposure
  field
    demandCount : Nat
    profileCount : Nat
    requiredKeyCount : Nat
    profileKeyCount : Nat
    matchedKeyPairCount : Nat
    physicalExposure : Nat

open TransitionExposure public

cartesianTransitionExposure :
  (demands profiles : Nat) → TransitionExposure
cartesianTransitionExposure demands profiles =
  transitionExposure
    demands profiles zero zero zero (demands * profiles)

indexedTransitionExposure :
  (demands profiles requiredKeys profileKeys matchedPairs : Nat) →
  TransitionExposure
indexedTransitionExposure demands profiles requiredKeys profileKeys matchedPairs =
  transitionExposure
    demands profiles requiredKeys profileKeys matchedPairs
    (requiredKeys + profileKeys + matchedPairs)

record IndexedSparseFrontierTransition : Set₁ where
  field
    RetentionDemand : Set
    RetentionProfile : Set
    CandidateDemand : Set
    CandidateProfile : Set

    legacyRetention : RetentionDemand → RetentionProfile → Set
    indexedRetention : RetentionDemand → RetentionProfile → Set
    retentionExact :
      ∀ demand profile →
      legacyRetention demand profile ≡ indexedRetention demand profile

    legacyCandidate : CandidateDemand → CandidateProfile → Set
    indexedCandidate : CandidateDemand → CandidateProfile → Set
    candidateExact :
      ∀ demand profile →
      legacyCandidate demand profile ≡ indexedCandidate demand profile

    legacyRetentionExposure : TransitionExposure
    indexedRetentionExposure : TransitionExposure
    legacyCandidateExposure : TransitionExposure
    indexedCandidateExposure : TransitionExposure

open IndexedSparseFrontierTransition public

sameRetentionRelation :
  (transition : IndexedSparseFrontierTransition) →
  ∀ demand profile →
  legacyRetention transition demand profile
    ≡ indexedRetention transition demand profile
sameRetentionRelation transition = retentionExact transition

sameCandidateRelation :
  (transition : IndexedSparseFrontierTransition) →
  ∀ demand profile →
  legacyCandidate transition demand profile
    ≡ indexedCandidate transition demand profile
sameCandidateRelation transition = candidateExact transition

-- A runtime claim of indexed transition work should report both stages through
-- key/match carriers.  This record intentionally does not assert that the
-- indexed exposure is numerically smaller for every dataset: wildcard demands
-- can legitimately remain broad.  Economy remains empirical; semantic parity
-- is theorem-level.
record IndexedExposureFactorisation
  (transition : IndexedSparseFrontierTransition) : Set where
  constructor indexedExposureFactorisation
  field
    retentionWorkFactors :
      physicalExposure (indexedRetentionExposure transition)
        ≡ requiredKeyCount (indexedRetentionExposure transition)
          + profileKeyCount (indexedRetentionExposure transition)
          + matchedKeyPairCount (indexedRetentionExposure transition)
    candidateWorkFactors :
      physicalExposure (indexedCandidateExposure transition)
        ≡ requiredKeyCount (indexedCandidateExposure transition)
          + profileKeyCount (indexedCandidateExposure transition)
          + matchedKeyPairCount (indexedCandidateExposure transition)

open IndexedExposureFactorisation public
