{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.DemandLocalWildcardHybridExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.AmbiguityPreservingBoundedWildcardExact as Wildcard
import DASHI.Cognition.PNF.DemandLocalWildcardTemporalOrderExact as Temporal
import DASHI.Cognition.PNF.HybridWildcardConsumerTupleParityExact as Consumer
import DASHI.Cognition.PNF.HybridWildcardDecisionRoutingExact as Routing

------------------------------------------------------------------------
-- CERTIFICATE FACTORISATION FOR THE DEMAND-LOCAL HYBRID
--
-- The optimisation is admissible only after four logically distinct questions
-- have been answered.  Keeping them separate prevents a fast benchmark from
-- being mistaken for a semantic proof.
------------------------------------------------------------------------

record DemandLocalHybridCertificate
  (Demand Object ActiveSegment Candidate Realization
   Membership CandidateCount UniqueTarget Outcome Provenance Residual : Set)
  : Set₂ where
  field
    temporalCarrier :
      Temporal.DemandLocalTemporalCarrier Demand Object ActiveSegment

    envelopeFor :
      Demand → Wildcard.MembershipEnvelope Candidate Realization

    invariantFor :
      (demand : Demand) → Wildcard.InvariantTopK (envelopeFor demand)

    boundedMembership : Demand → Membership
    legacyMembership : Demand → Membership
    membershipExact :
      (demand : Demand) → boundedMembership demand ≡ legacyMembership demand

    consumerDerivation :
      Consumer.ConsumerDerivation
        Membership CandidateCount UniqueTarget Outcome Provenance

    residual : Demand → Residual

open DemandLocalHybridCertificate public

------------------------------------------------------------------------
-- Once the demand-local carrier and MUST=MAY membership certificate have been
-- established, full consumer parity follows from the existing derivation
-- theorem.  This theorem still does not assert any physical speedup.
------------------------------------------------------------------------

demandLocalCertifiedConsumerTupleIsExact :
  ∀ {Demand Object ActiveSegment Candidate Realization
     Membership CandidateCount UniqueTarget Outcome Provenance Residual : Set}
    (certificate :
      DemandLocalHybridCertificate
        Demand Object ActiveSegment Candidate Realization
        Membership CandidateCount UniqueTarget Outcome Provenance Residual) →
    (demand : Demand) →
  Consumer.deriveConsumerObservation
    (consumerDerivation certificate)
    (boundedMembership certificate demand)
    ≡
  Consumer.deriveConsumerObservation
    (consumerDerivation certificate)
    (legacyMembership certificate demand)
demandLocalCertifiedConsumerTupleIsExact certificate demand =
  Consumer.membershipParityLiftsToFullConsumerTuple
    (consumerDerivation certificate)
    (membershipExact certificate demand)

------------------------------------------------------------------------
-- A runtime route remains a separate proof object.  The certified route may use
-- the bounded observation; every uncertified route must carry the residual and
-- expose the legacy observation unchanged.
------------------------------------------------------------------------

record DemandLocalHybridDispatcher
  (Demand Observation Residual : Set) : Set₁ where
  field
    decision : Demand → Routing.HybridDecision Observation Residual

open DemandLocalHybridDispatcher public

demandLocalDispatcherPreservesConsumerObservation :
  ∀ {Demand Observation Residual : Set}
    (dispatcher : DemandLocalHybridDispatcher Demand Observation Residual) →
    (demand : Demand) →
  Routing.chosenObservation (decision dispatcher demand)
    ≡ Routing.legacyObservationOf (decision dispatcher demand)
demandLocalDispatcherPreservesConsumerObservation dispatcher demand =
  Routing.hybridDecisionPreservesDeclaredConsumerObservation
    (decision dispatcher demand)

------------------------------------------------------------------------
-- Performance is deliberately absent from the semantic certificate.  A runtime
-- may attach a cost receipt after the proofs above; no constructor here allows
-- cost to manufacture temporal exactness, membership exactness or route safety.
------------------------------------------------------------------------

data PerformanceImpliesSemanticCertificatePermission : Set where

performanceCannotManufactureSemanticCertificate :
  PerformanceImpliesSemanticCertificatePermission → ⊥
performanceCannotManufactureSemanticCertificate ()
