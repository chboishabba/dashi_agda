module DASHI.Physics.Plasma.Phase243PhysicalRoadmapStatusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- TERMINAL STATUS OWNER FOR THE CURRENT PHASE243 CONFINEMENT ROADMAP
--
-- Paid on this branch:
--   630 -> 270 -> 243 -> 54 finite/action search compression;
--   periodic-consumer descent through the 54 quotient;
--   positive non-axisymmetric continuous fibres;
--   declared-axis Pareto routing over ABC allocations;
--   winding-surface current-potential inverse on shortlisted fibres.
--
-- First unpaid physical producer:
--   same-object finite-beta free-boundary B_total = B_coil + B_plasma
--   with the selected ABC allocation and kinetic/stability closure.
--
-- Downstream of that producer, and not replaceable by the proxy field:
--   zero-bounce / trapped fraction / J_parallel / FOW / EP / collisions;
--   same-normalization best-known-reference comparison.
------------------------------------------------------------------------

record Phase243PhysicalRoadmapStatus : Set where
  constructor phase243-physical-roadmap-status
  field
    phaseStable630CarrierPaid : Bool
    phaseStable630CarrierPaidIsTrue : phaseStable630CarrierPaid ≡ true

    rook270AndCore243Paid : Bool
    rook270AndCore243PaidIsTrue : rook270AndCore243Paid ≡ true

    periodicConsumerCore54QuotientPaid : Bool
    periodicConsumerCore54QuotientPaidIsTrue :
      periodicConsumerCore54QuotientPaid ≡ true

    nonAxisymmetricContinuousFibreSearchPaid : Bool
    nonAxisymmetricContinuousFibreSearchPaidIsTrue :
      nonAxisymmetricContinuousFibreSearchPaid ≡ true

    declaredAxisParetoRoutingPaid : Bool
    declaredAxisParetoRoutingPaidIsTrue : declaredAxisParetoRoutingPaid ≡ true

    currentPotentialCoilRoutingPaid : Bool
    currentPotentialCoilRoutingPaidIsTrue : currentPotentialCoilRoutingPaid ≡ true

    sameObjectFreeBoundaryEquilibriumPaid : Bool
    sameObjectFreeBoundaryEquilibriumPaidIsFalse :
      sameObjectFreeBoundaryEquilibriumPaid ≡ false

    producedFieldOrbitAcceptancePaid : Bool
    producedFieldOrbitAcceptancePaidIsFalse :
      producedFieldOrbitAcceptancePaid ≡ false

    sameBestKnownReferencePaid : Bool
    sameBestKnownReferencePaidIsFalse : sameBestKnownReferencePaid ≡ false

    moreFiniteCombinatoricsIsCurrentBottleneck : Bool
    moreFiniteCombinatoricsIsCurrentBottleneckIsFalse :
      moreFiniteCombinatoricsIsCurrentBottleneck ≡ false

canonicalPhase243PhysicalRoadmapStatus : Phase243PhysicalRoadmapStatus
canonicalPhase243PhysicalRoadmapStatus =
  phase243-physical-roadmap-status
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

firstUnpaidProducer : String
firstUnpaidProducer =
  "Solve the shortlisted coil current configuration and plasma current/pressure/flow/anisotropy together as one finite-beta free-boundary equilibrium, producing B_total = B_coil + B_plasma on the same geometry and normalization."

stoppingRule : String
stoppingRule =
  "Do not count additional finite carrier arithmetic, quotient naming, Pareto rescalarization, or target-field optimization as physical progress unless it advances the same-object free-boundary producer or a downstream produced-field consumer."

sourceAttributionRule : String
sourceAttributionRule =
  "External sources retain their own authority role: measured observation, simulation/comparison, analytic theory, planned measurement and company statement are not interchangeable. Script-produced numerical artifacts do not inherit source authority, and source claims do not become artifact proofs."
