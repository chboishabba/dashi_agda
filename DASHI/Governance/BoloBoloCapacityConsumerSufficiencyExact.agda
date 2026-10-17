module DASHI.Governance.BoloBoloCapacityConsumerSufficiencyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment
import DASHI.Governance.BoloBoloExperimentalCoordinateDiscriminatorExact as Coordinate

------------------------------------------------------------------------
-- CAPACITY-SENSITIVE CONSUMER SUFFICIENCY
--
-- The previous experimental-coordinate owner gives a concrete collision:
-- duration, even joined with incidence, may identify worlds whose interface
-- capacity/backlog differ.  This owner strengthens that witness using the
-- repository's generic consumer-relative least-sufficiency theorem.
--
-- The declared consumer is deliberately narrow: it asks only for the triple
-- (measured interface capacity, peak concurrent boundary demand, backlog).
-- Being sufficient for this consumer is not world completeness and does not
-- establish cost, causal effect, legitimacy, viability, or political quality.
------------------------------------------------------------------------

CapacityConsumerOutcome : Set
CapacityConsumerOutcome = Nat × (Nat × Nat)

capacitySensitiveConsumer :
  Experiment.OutcomeVector → CapacityConsumerOutcome
capacitySensitiveConsumer world =
  Experiment.interfaceCapacity world ,
  (Experiment.peakBoundaryDemand world , Experiment.interfaceBacklog world)

capacityConsumerIsLeast :
  Descent.LeastSufficientConsumerObserver capacitySensitiveConsumer
capacityConsumerIsLeast =
  Descent.canonicalConsumerObserverIsLeast capacitySensitiveConsumer

------------------------------------------------------------------------
-- Universal information-order consequence.
--
-- Any observation surface that is sufficient for this declared consumer must
-- refine the canonical consumer observation itself.  This is stronger than a
-- single bad-fibre example, while remaining consumer-relative.
------------------------------------------------------------------------

everyCapacityAdequateObserverRefinesCanonical :
  ∀ {Surface : Set}
    (observe : Experiment.OutcomeVector → Surface) →
  Descent.ConsumerSufficient observe capacitySensitiveConsumer →
  Observer.Refines capacitySensitiveConsumer observe
everyCapacityAdequateObserverRefinesCanonical observe sufficient =
  Descent.belowEverySufficient capacityConsumerIsLeast observe sufficient

------------------------------------------------------------------------
-- Existing finite collisions instantiate non-descent for the capacity
-- consumer.  The two synthetic outcomes have the same duration and incidence,
-- but capacity/backlog differ.
------------------------------------------------------------------------

durationCapacityNonDescent :
  Descent.ConsumerNonDescentWitness
    Coordinate.durationOnlyObserver
    capacitySensitiveConsumer
durationCapacityNonDescent =
  Descent.consumerNonDescentWitness
    Coordinate.leftSyntheticOutcome
    Coordinate.rightSyntheticOutcome
    Coordinate.sameDurationCollision
    (λ ())

durationIncidenceCapacityNonDescent :
  Descent.ConsumerNonDescentWitness
    Coordinate.durationIncidenceObserver
    capacitySensitiveConsumer
durationIncidenceCapacityNonDescent =
  Descent.consumerNonDescentWitness
    Coordinate.leftSyntheticOutcome
    Coordinate.rightSyntheticOutcome
    Coordinate.sameDurationIncidenceCollision
    (λ ())

durationCannotBeCapacityConsumerSufficient :
  Descent.ConsumerSufficient
    Coordinate.durationOnlyObserver
    capacitySensitiveConsumer → ⊥
durationCannotBeCapacityConsumerSufficient =
  Descent.nonDescentWitnessBlocksSufficiency durationCapacityNonDescent

durationIncidenceCannotBeCapacityConsumerSufficient :
  Descent.ConsumerSufficient
    Coordinate.durationIncidenceObserver
    capacitySensitiveConsumer → ⊥
durationIncidenceCannotBeCapacityConsumerSufficient =
  Descent.nonDescentWitnessBlocksSufficiency
    durationIncidenceCapacityNonDescent

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record CapacityConsumerBoundary : Set where
  constructor capacity-consumer-boundary
  field
    capacityConsumerLeastSufficientPaid : Bool
    everyCapacityAdequateObserverRefinesCanonicalPaid : Bool
    durationObserverConsumerSufficient : Bool
    durationIncidenceObserverConsumerSufficient : Bool
    leastSufficientMeansWorldComplete : Bool
    capacityConsumerDeterminesCoordinationCost : Bool
    capacityConsumerIdentifiesCausalEffect : Bool
    syntheticWitnessCreatesEmpiricalCapacityResult : Bool
    targetCapacityBacklogCalibrationStillRequired : Bool

open CapacityConsumerBoundary public

canonicalCapacityConsumerBoundary : CapacityConsumerBoundary
canonicalCapacityConsumerBoundary =
  capacity-consumer-boundary
    true true
    false false false false false false
    true
