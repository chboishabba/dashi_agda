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
--   winding-surface current-potential inverse on shortlisted fibres;
--   exact six-candidate P5 input manifest;
--   exhaustive solve-or-reject P5 result ABI;
--   P6 produced-field orbit ABI requiring a solved P5 case;
--   source-typed P7 SOTA benchmark ABI;
--   consumer-relative downstream reopening rule.
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

    freeBoundarySixInputManifestPaid : Bool
    freeBoundarySixInputManifestPaidIsTrue : freeBoundarySixInputManifestPaid ≡ true

    freeBoundarySolveRejectABIPaid : Bool
    freeBoundarySolveRejectABIPaidIsTrue : freeBoundarySolveRejectABIPaid ≡ true

    producedFieldOrbitABIPaid : Bool
    producedFieldOrbitABIPaidIsTrue : producedFieldOrbitABIPaid ≡ true

    sourceTypedSOTABenchmarkABIPaid : Bool
    sourceTypedSOTABenchmarkABIPaidIsTrue : sourceTypedSOTABenchmarkABIPaid ≡ true

    downstreamConsumerReopeningPaid : Bool
    downstreamConsumerReopeningPaidIsTrue : downstreamConsumerReopeningPaid ≡ true

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
  "Execute the frozen six candidate coil/plasma configurations through one declared finite-beta free-boundary solver contract. Every row must return either SolvedFreeBoundaryCase or a typed RejectedFreeBoundaryCase. A solved row must produce B_total = B_coil + B_plasma on the same geometry and normalization with the declared ABC allocation and stability/kinetic closure receipts."

nextDownstreamProducer : String
nextDownstreamProducer =
  "For each solved P5 row, construct the ProducedFieldOrbitAtlas on that produced B_total. Only then acquire the external benchmark coordinates needed to instantiate same-normalization P7 comparison rows."

stoppingRule : String
stoppingRule =
  "Do not count additional finite carrier arithmetic, quotient naming, Pareto rescalarization, target-field optimization, benchmark citation collection, or interface elaboration as physical progress unless it advances a frozen P5 row to solved/rejected status or advances a solved row through a produced-field consumer."

sourceAttributionRule : String
sourceAttributionRule =
  "External sources retain their own authority role: measured observation, simulation/comparison, analytic theory, planned measurement and company statement are not interchangeable. Script-produced numerical artifacts do not inherit source authority; source claims do not become artifact proofs; a benchmark citation does not instantiate a same-normalization comparison without the required external configuration/population/data coordinates."
