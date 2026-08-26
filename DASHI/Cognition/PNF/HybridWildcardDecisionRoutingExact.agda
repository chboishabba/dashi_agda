{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.HybridWildcardDecisionRoutingExact where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact as Wildcard

------------------------------------------------------------------------
-- Proof-directed hybrid routing.
--
-- Cross-pollination sources:
--
-- * PolicyRelativeProjectionSafety: an observation may be sufficient to choose
--   one restricted policy without reconstructing the whole fine state.
-- * AuthorityRoutingProjectionSafetyExact / situated-policy routing: erased
--   distinctions may not be ignored when they can change the required route.
-- * ReopenableEvidenceFibre: bounded execution is subordinate to semantic
--   possibility; omitted/residual possibilities are not refuted by pruning.
-- * GovernedEpistemicInquiry: representation, query sufficiency and policy
--   safety are separate certificates rather than one collapsed status.
--
-- Applied to the sparse wildcard frontier, the MUST=MAY certificate is therefore
-- not a fine-score reconstruction theorem.  It is a routing certificate:
-- certified fibres may use the bounded policy; uncertified fibres retain their
-- residual and route to the legacy authority-preserving policy.
------------------------------------------------------------------------

data WildcardExecutionRoute : Set where
  certifiedBoundedRoute : WildcardExecutionRoute
  residualLegacyRoute : WildcardExecutionRoute

routeFromOutcome :
  ∀ {Candidate Realization : Set}
    {envelope : Wildcard.MembershipEnvelope Candidate Realization} →
  Wildcard.BoundedWildcardOutcome envelope →
  WildcardExecutionRoute
routeFromOutcome (Wildcard.certifiedTopK invariant) = certifiedBoundedRoute
routeFromOutcome Wildcard.ambiguousResidual = residualLegacyRoute

------------------------------------------------------------------------
-- A hybrid decision carries the observation required by the declared consumer.
-- The bounded branch is admitted only together with an equality witness against
-- the legacy consumer observation.  The fallback branch literally returns the
-- legacy observation and carries the unresolved residual separately.
------------------------------------------------------------------------

data HybridDecision (Observation Residual : Set) : Set where
  boundedCertified :
    (boundedObservation legacyObservation : Observation) →
    boundedObservation ≡ legacyObservation →
    HybridDecision Observation Residual

  residualFallback :
    (legacyObservation : Observation) →
    Residual →
    HybridDecision Observation Residual

routeOf :
  ∀ {Observation Residual : Set} →
  HybridDecision Observation Residual →
  WildcardExecutionRoute
routeOf (boundedCertified bounded legacy same) = certifiedBoundedRoute
routeOf (residualFallback legacy residual) = residualLegacyRoute

chosenObservation :
  ∀ {Observation Residual : Set} →
  HybridDecision Observation Residual →
  Observation
chosenObservation (boundedCertified bounded legacy same) = bounded
chosenObservation (residualFallback legacy residual) = legacy

legacyObservationOf :
  ∀ {Observation Residual : Set} →
  HybridDecision Observation Residual →
  Observation
legacyObservationOf (boundedCertified bounded legacy same) = legacy
legacyObservationOf (residualFallback legacy residual) = legacy

hybridDecisionPreservesDeclaredConsumerObservation :
  ∀ {Observation Residual : Set}
    (decision : HybridDecision Observation Residual) →
  chosenObservation decision ≡ legacyObservationOf decision
hybridDecisionPreservesDeclaredConsumerObservation
  (boundedCertified bounded legacy same) = same
hybridDecisionPreservesDeclaredConsumerObservation
  (residualFallback legacy residual) = refl

------------------------------------------------------------------------
-- Whole-workload composition theorem.
--
-- This is the production theorem shape.  Exactness is not a statistical claim
-- about the fraction certified.  Every demand is exact because each demand is
-- either accompanied by a bounded-equality certificate or routed unchanged to
-- the legacy observation.
------------------------------------------------------------------------

record ProofDirectedHybridDispatcher
  (Demand Observation Residual : Set) : Set₁ where
  field
    decide : Demand → HybridDecision Observation Residual

open ProofDirectedHybridDispatcher public

hybridDispatcherIsExtensionallyExact :
  ∀ {Demand Observation Residual : Set}
    (dispatcher : ProofDirectedHybridDispatcher Demand Observation Residual) →
    (demand : Demand) →
  chosenObservation (decide dispatcher demand)
    ≡ legacyObservationOf (decide dispatcher demand)
hybridDispatcherIsExtensionallyExact dispatcher demand =
  hybridDecisionPreservesDeclaredConsumerObservation
    (decide dispatcher demand)

------------------------------------------------------------------------
-- Residual routing is not semantic failure.
--
-- The fallback constructor carries a residual but contains no constructor that
-- can turn that residual into negative evidence, failed demand, or scalar
-- identity.  It merely chooses the slower execution policy.
------------------------------------------------------------------------

data ResidualFallbackFailurePermission : Set where

residualFallbackCannotManufactureFailure :
  ResidualFallbackFailurePermission →
  ∀ {Observation Residual : Set} →
  HybridDecision Observation Residual
residualFallbackCannotManufactureFailure ()

------------------------------------------------------------------------
-- Consumer-observation boundary.
--
-- The theorem intentionally says nothing about reconstructing floating planner
-- scores, representative provenance rows, or fine execution history.  Those may
-- remain in the residual/receipt fibre while the declared resolution consumer
-- sees the same membership/count/unique-target/outcome observation.
------------------------------------------------------------------------

record ResolutionConsumerObservation
  (Membership CandidateCount UniqueTarget Outcome Provenance : Set) : Set where
  constructor resolutionConsumerObservation
  field
    membership : Membership
    candidateCount : CandidateCount
    uniqueTarget : UniqueTarget
    outcome : Outcome
    membershipProvenance : Provenance

open ResolutionConsumerObservation public
