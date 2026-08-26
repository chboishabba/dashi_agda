{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.HybridWildcardConsumerTupleParityExact where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.HybridWildcardDecisionRoutingExact as Routing

------------------------------------------------------------------------
-- FULL RESOLUTION-CONSUMER PARITY
--
-- Cross-pollinated boundary:
--   * FibreRestrictionCore: restricting a fibre does not reconstruct its carrier.
--   * PolicyRelativeProjectionSafety: a coarse observation may be sufficient for
--     one declared policy without being a complete fine-state representation.
--   * ReopenableEvidenceFibre: execution metadata / pruning is subordinate to
--     semantic possibility and cannot manufacture refutation.
--
-- Hence the bounded wildcard path need not reconstruct the legacy floating
-- candidate-score row.  It must preserve the declared resolution consumer:
-- membership+membership provenance, candidate count, unique target and outcome.
------------------------------------------------------------------------

record ConsumerDerivation
  (Membership CandidateCount UniqueTarget Outcome Provenance : Set) : Set₁ where
  field
    deriveCandidateCount : Membership → CandidateCount
    deriveUniqueTarget : Membership → UniqueTarget
    deriveOutcome : Membership → Outcome
    deriveMembershipProvenance : Membership → Provenance

open ConsumerDerivation public

deriveConsumerObservation :
  ∀ {Membership CandidateCount UniqueTarget Outcome Provenance : Set} →
  ConsumerDerivation Membership CandidateCount UniqueTarget Outcome Provenance →
  Membership →
  Routing.ResolutionConsumerObservation
    Membership CandidateCount UniqueTarget Outcome Provenance
deriveConsumerObservation derivation membership =
  Routing.resolutionConsumerObservation
    membership
    (deriveCandidateCount derivation membership)
    (deriveUniqueTarget derivation membership)
    (deriveOutcome derivation membership)
    (deriveMembershipProvenance derivation membership)

membershipParityLiftsToFullConsumerTuple :
  ∀ {Membership CandidateCount UniqueTarget Outcome Provenance : Set}
    (derivation :
      ConsumerDerivation Membership CandidateCount UniqueTarget Outcome Provenance)
    {boundedMembership legacyMembership : Membership} →
  boundedMembership ≡ legacyMembership →
  deriveConsumerObservation derivation boundedMembership
    ≡ deriveConsumerObservation derivation legacyMembership
membershipParityLiftsToFullConsumerTuple derivation refl = refl

------------------------------------------------------------------------
-- Certified branch / residual branch composition.
------------------------------------------------------------------------

record CertifiedConsumerTupleParity
  (Membership CandidateCount UniqueTarget Outcome Provenance : Set) : Set₁ where
  field
    derivation :
      ConsumerDerivation Membership CandidateCount UniqueTarget Outcome Provenance
    boundedMembership : Membership
    legacyMembership : Membership
    membershipParity : boundedMembership ≡ legacyMembership

open CertifiedConsumerTupleParity public

certifiedConsumerTupleIsExact :
  ∀ {Membership CandidateCount UniqueTarget Outcome Provenance : Set}
    (certificate :
      CertifiedConsumerTupleParity
        Membership CandidateCount UniqueTarget Outcome Provenance) →
  deriveConsumerObservation (derivation certificate) (boundedMembership certificate)
    ≡
  deriveConsumerObservation (derivation certificate) (legacyMembership certificate)
certifiedConsumerTupleIsExact certificate =
  membershipParityLiftsToFullConsumerTuple
    (derivation certificate)
    (membershipParity certificate)

-- The whole dispatcher remains exact even when only a subset is certifiable:
-- certified fibres use their proved-equal bounded tuple; uncertified fibres use
-- the legacy tuple unchanged.  The fraction taking either route is irrelevant
-- to semantic exactness.
wholeHybridConsumerTupleIsExact :
  ∀ {Observation Residual : Set}
    (decision : Routing.HybridDecision Observation Residual) →
  Routing.chosenObservation decision ≡ Routing.legacyObservationOf decision
wholeHybridConsumerTupleIsExact =
  Routing.hybridDecisionPreservesDeclaredConsumerObservation

------------------------------------------------------------------------
-- Planner score is intentionally outside this theorem.  There is no eliminator
-- from consumer-tuple equality to equality of hidden/floating representative
-- metadata; that information remains in the execution/provenance residual.
------------------------------------------------------------------------

data FineRepresentativeReconstructionPermission : Set where

consumerTupleParityCannotManufactureFineRepresentative :
  FineRepresentativeReconstructionPermission →
  ∀ {A : Set} → A
consumerTupleParityCannotManufactureFineRepresentative ()
