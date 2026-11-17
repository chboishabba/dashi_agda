module DASHI.Governance.BoloBoloExperimentalCoordinateDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment
import DASHI.Governance.BoloBoloGovernanceMetricProvenanceExact as Metric

------------------------------------------------------------------------
-- GOVERNANCE EXPERIMENTAL COORDINATE DISCRIMINATOR
--
-- Reuses the repo-native ExperimentalCoordinateDesign abstraction to prove a
-- concrete information-design point for the bolo pilot: equal meeting duration
-- can hide materially different interface-capacity / backlog states.  This is a
-- finite DASHI witness, not empirical evidence about any real institution.
------------------------------------------------------------------------

data GovernanceExperimentCoordinate : Set where
  durationCoordinate : GovernanceExperimentCoordinate
  incidenceCoordinate : GovernanceExperimentCoordinate
  capacityCoordinate : GovernanceExperimentCoordinate
  backlogCoordinate : GovernanceExperimentCoordinate

governanceCoordinateRole :
  GovernanceExperimentCoordinate → Design.CoordinateRole
governanceCoordinateRole durationCoordinate = Design.measuredObservable
governanceCoordinateRole incidenceCoordinate = Design.measuredObservable
governanceCoordinateRole capacityCoordinate = Design.measuredObservable
governanceCoordinateRole backlogCoordinate = Design.measuredObservable

governanceCoordinateDimension :
  GovernanceExperimentCoordinate → Metric.GovernanceMetricRole
governanceCoordinateDimension durationCoordinate = Metric.observedDurationMinutes
governanceCoordinateDimension incidenceCoordinate = Metric.incidenceEdgeCount
governanceCoordinateDimension capacityCoordinate = Metric.interfaceCapacity
governanceCoordinateDimension backlogCoordinate = Metric.backlogCount

governanceCoordinateRead :
  GovernanceExperimentCoordinate → Experiment.OutcomeVector → Nat
governanceCoordinateRead durationCoordinate = Experiment.durationMinutes
governanceCoordinateRead incidenceCoordinate = Experiment.incidenceEdges
governanceCoordinateRead capacityCoordinate = Experiment.interfaceCapacity
governanceCoordinateRead backlogCoordinate = Experiment.interfaceBacklog

identityControl : ⊤ → Experiment.OutcomeVector → Experiment.OutcomeVector
identityControl tt world = world

governanceCoordinateReference : GovernanceExperimentCoordinate → String
governanceCoordinateReference durationCoordinate = "paired-pilot:duration-minutes"
governanceCoordinateReference incidenceCoordinate = "paired-pilot:participant-issue-incidence"
governanceCoordinateReference capacityCoordinate = "paired-pilot:interface-capacity"
governanceCoordinateReference backlogCoordinate = "paired-pilot:interface-backlog"

governanceDimensionReference : GovernanceExperimentCoordinate → String
governanceDimensionReference durationCoordinate = "metric-role:observed-duration-minutes"
governanceDimensionReference incidenceCoordinate = "metric-role:incidence-edge-count"
governanceDimensionReference capacityCoordinate = "metric-role:interface-capacity"
governanceDimensionReference backlogCoordinate = "metric-role:backlog-count"

governanceCalibrationReference : GovernanceExperimentCoordinate → String
governanceCalibrationReference durationCoordinate = "target-study duration measurement protocol required"
governanceCalibrationReference incidenceCoordinate = "target-study incidence coding protocol required"
governanceCalibrationReference capacityCoordinate = "target-study interface-capacity protocol required"
governanceCalibrationReference backlogCoordinate = "target-study backlog protocol required"

identityControlReference : ⊤ → String
identityControlReference tt = "identity/no-intervention control used only for finite discriminator witness"

governanceExperimentalCoordinateDesign :
  Design.ExperimentalCoordinateDesign
    Experiment.OutcomeVector
    ⊤
    Nat
    Metric.GovernanceMetricRole
governanceExperimentalCoordinateDesign =
  Design.experimentalCoordinateDesign
    GovernanceExperimentCoordinate
    governanceCoordinateRole
    governanceCoordinateDimension
    governanceCoordinateRead
    identityControl
    governanceCoordinateReference
    governanceDimensionReference
    governanceCalibrationReference
    identityControlReference

------------------------------------------------------------------------
-- Exact synthetic collision.
--
-- Same duration (120) and same incidence (30), but different interface
-- capacity/backlog.  Duration-only and duration+incidence summaries therefore
-- cannot certify the capacity-sensitive state.
------------------------------------------------------------------------

leftSyntheticOutcome : Experiment.OutcomeVector
leftSyntheticOutcome =
  Experiment.outcomeVector
    120 2 1 4 3 30 10 5 12 10 2 4

rightSyntheticOutcome : Experiment.OutcomeVector
rightSyntheticOutcome =
  Experiment.outcomeVector
    120 2 1 4 3 30 10 5 12 20 5 4

durationOnlyObserver : Experiment.OutcomeVector → Nat
durationOnlyObserver = Experiment.durationMinutes

durationIncidenceObserver : Experiment.OutcomeVector → Nat × Nat
durationIncidenceObserver world =
  Experiment.durationMinutes world , Experiment.incidenceEdges world

sameDurationCollision :
  durationOnlyObserver leftSyntheticOutcome
  ≡ durationOnlyObserver rightSyntheticOutcome
sameDurationCollision = refl

sameDurationIncidenceCollision :
  durationIncidenceObserver leftSyntheticOutcome
  ≡ durationIncidenceObserver rightSyntheticOutcome
sameDurationIncidenceCollision = refl

capacitySeparatesDurationCollision :
  Design.CoordinateSeparatesCollision
    governanceExperimentalCoordinateDesign
    durationOnlyObserver
capacitySeparatesDurationCollision =
  Design.coordinateSeparatesCollision
    capacityCoordinate
    leftSyntheticOutcome
    rightSyntheticOutcome
    refl
    (λ ())

backlogSeparatesDurationCollision :
  Design.CoordinateSeparatesCollision
    governanceExperimentalCoordinateDesign
    durationOnlyObserver
backlogSeparatesDurationCollision =
  Design.coordinateSeparatesCollision
    backlogCoordinate
    leftSyntheticOutcome
    rightSyntheticOutcome
    refl
    (λ ())

capacitySeparatesDurationIncidenceCollision :
  Design.CoordinateSeparatesCollision
    governanceExperimentalCoordinateDesign
    durationIncidenceObserver
capacitySeparatesDurationIncidenceCollision =
  Design.coordinateSeparatesCollision
    capacityCoordinate
    leftSyntheticOutcome
    rightSyntheticOutcome
    refl
    (λ ())

------------------------------------------------------------------------
-- Boundary / interpretation.
------------------------------------------------------------------------

record GovernanceCoordinateBoundary : Set where
  constructor governance-coordinate-boundary
  field
    sameDurationCollisionPaid : Bool
    sameDurationIncidenceCollisionPaid : Bool
    capacityCoordinateSeparatesCollisionPaid : Bool
    backlogCoordinateSeparatesCollisionPaid : Bool
    durationOnlyObserverSufficientForCapacityConsumer : Bool
    durationIncidenceObserverSufficientForCapacityConsumer : Bool
    addedCoordinateAutomaticallyCreatesEmpiricalObservation : Bool
    syntheticCollisionIsEmpiricalPerformanceResult : Bool
    capacityProtocolStillRequiresTargetCalibration : Bool
    backlogProtocolStillRequiresTargetCalibration : Bool

open GovernanceCoordinateBoundary public

canonicalGovernanceCoordinateBoundary : GovernanceCoordinateBoundary
canonicalGovernanceCoordinateBoundary =
  governance-coordinate-boundary
    true true true true
    false false false false
    true true

canonicalBoloExperimentalCoordinateDiscriminatorReceipt :
  GenericReceipt.GenericReceipt
canonicalBoloExperimentalCoordinateDiscriminatorReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo paired-pilot experimental-coordinate discriminator"
    "DASHI.Governance.BoloBoloExperimentalCoordinateDiscriminatorExact"
    "governanceExperimentalCoordinateDesign / capacitySeparatesDurationCollision / backlogSeparatesDurationCollision / canonicalGovernanceCoordinateBoundary"
    "instantiates the repo-native experimental-coordinate design on paired-governance outcomes and gives an exact finite collision: two synthetic worlds have identical duration and incidence summaries while interface capacity and backlog differ, so capacity/backlog coordinates strictly increase observational resolution for capacity-sensitive evaluation"
    "the witness is synthetic and creates no empirical performance result, target capacity, backlog estimate or causal effect; real use still requires calibrated target measurement protocols and the existing causal-identification/promotion gates"
    "agda -i . DASHI/Governance/BoloBoloExperimentalCoordinateDiscriminatorRegression.agda"
