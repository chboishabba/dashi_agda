{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.JetEngineCanonicalMissionEnergyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.JetEngineFlowArchitectureExact as Jet
import DASHI.Physics.Propulsion.JetEngineIndustrialEnergyBidiExact as Industrial

------------------------------------------------------------------------
-- CANONICAL MISSION-ENERGY CONSUMER
--
-- Recent proof-search audits elsewhere in DASHI make a useful general point:
-- a successful producer route is not thereby a mandatory residual.  For a jet
-- engine the terminal engineering/climate consumer normally needs a SAME
-- mission service/fuel/emissions trajectory.  A full Brayton reconstruction,
-- compressor map, blade model, or certification model may produce that payment,
-- but none is definitionally required by the consumer merely because it is a
-- useful way of obtaining it.
------------------------------------------------------------------------

data MissionSegmentKind : Set where
  groundIdle : MissionSegmentKind
  takeoff : MissionSegmentKind
  climb : MissionSegmentKind
  cruise : MissionSegmentKind
  descent : MissionSegmentKind
  approach : MissionSegmentKind

data MissionServiceKind : Set where
  passengerTransport : MissionServiceKind
  freightTransport : MissionServiceKind
  testFlight : MissionServiceKind
  otherService : MissionServiceKind

record MissionSegment : Set where
  constructor mission-segment
  field
    segmentKind : MissionSegmentKind
    durationCode : Nat
    distanceCode : Nat
    thrustDemandCode : Nat
    fuelBurnCode : Nat
    sourceObject : String

open MissionSegment public

record MissionTrajectory : Set where
  constructor mission-trajectory
  field
    missionIdentity : String
    serviceKind : MissionServiceKind
    serviceDemandCode : Nat
    segments : List MissionSegment
    totalFuelBurnCode : Nat
    sameAircraftEngineConfiguration : Bool
    sameAircraftEngineConfigurationIsTrue :
      sameAircraftEngineConfiguration ≡ true

open MissionTrajectory public

------------------------------------------------------------------------
-- The canonical payment is deliberately small.  Detailed internal engine
-- physics can be upstream, while the downstream resource/climate consumer gets
-- exactly the mission coordinates it needs.
------------------------------------------------------------------------

record MissionEnergyPayment : Set where
  constructor mission-energy-payment
  field
    trajectory : MissionTrajectory
    usefulServiceSatisfied : Bool
    usefulServiceSatisfiedIsTrue : usefulServiceSatisfied ≡ true
    fuelBurnSameMission : Bool
    fuelBurnSameMissionIsTrue : fuelBurnSameMission ≡ true
    fuelPathway : Industrial.FuelPathway
    fuelPathwaySameMission : Bool
    fuelPathwaySameMissionIsTrue : fuelPathwaySameMission ≡ true
    emissionsSameMission : Bool
    emissionsSameMissionIsTrue : emissionsSameMission ≡ true
    evidenceReference : String

open MissionEnergyPayment public

record CanonicalMissionEnergyConsumer : Set where
  constructor canonical-mission-energy-consumer
  field
    payment : MissionEnergyPayment
    serviceCoordinatePaid : Bool
    serviceCoordinatePaidIsTrue : serviceCoordinatePaid ≡ true
    fuelCoordinatePaid : Bool
    fuelCoordinatePaidIsTrue : fuelCoordinatePaid ≡ true
    sameMissionCarrierPaid : Bool
    sameMissionCarrierPaidIsTrue : sameMissionCarrierPaid ≡ true

open CanonicalMissionEnergyConsumer public

------------------------------------------------------------------------
-- Producer families.  These are routes to a payment, not prerequisites baked
-- into the consumer type.
------------------------------------------------------------------------

data MissionEnergyProducerFamily : Set where
  stationThermodynamicProducer : MissionEnergyProducerFamily
  idealBraytonProducer : MissionEnergyProducerFamily
  compressorTurbineMapProducer : MissionEnergyProducerFamily
  installedPerformanceProducer : MissionEnergyProducerFamily
  flightTelemetryProducer : MissionEnergyProducerFamily
  operatorFuelRecordProducer : MissionEnergyProducerFamily

record MissionEnergyProducerRoute : Set where
  constructor mission-energy-producer-route
  field
    family : MissionEnergyProducerFamily
    sourceObject : String
    sameMissionResolved : Bool
    producesMissionEnergyPayment : Bool

open MissionEnergyProducerRoute public

------------------------------------------------------------------------
-- Existing engine-level receipts remain useful but do not manufacture the
-- outer mission object.  This blocks the common WrongType from rated or
-- component performance to realised mission fuel burn.
------------------------------------------------------------------------

data EnginePerformanceCreatesMissionIdentityPermission : Set where

data IdealCycleMandatoryForMissionPaymentPermission : Set where

data CompressorMapMandatoryForMissionPaymentPermission : Set where

data LowerSpecificFuelUseImpliesLowerAbsoluteFleetFuelPermission : Set where

data MissionFuelBurnAloneDeterminesClimateForcingPermission : Set where

enginePerformanceDoesNotCreateMissionIdentity :
  EnginePerformanceCreatesMissionIdentityPermission → ⊥
enginePerformanceDoesNotCreateMissionIdentity ()

idealCycleIsNotDefinitionallyMandatory :
  IdealCycleMandatoryForMissionPaymentPermission → ⊥
idealCycleIsNotDefinitionallyMandatory ()

compressorMapIsNotDefinitionallyMandatory :
  CompressorMapMandatoryForMissionPaymentPermission → ⊥
compressorMapIsNotDefinitionallyMandatory ()

lowerSpecificFuelUseDoesNotProveLowerAbsoluteFleetFuel :
  LowerSpecificFuelUseImpliesLowerAbsoluteFleetFuelPermission → ⊥
lowerSpecificFuelUseDoesNotProveLowerAbsoluteFleetFuel ()

missionFuelBurnDoesNotAloneDetermineClimateForcing :
  MissionFuelBurnAloneDeterminesClimateForcingPermission → ⊥
missionFuelBurnDoesNotAloneDetermineClimateForcing ()

------------------------------------------------------------------------
-- Same-object weld from an internal engine execution into a mission segment.
-- It is intentionally an interface receipt: the execution and segment must be
-- identified by an external producer; matching scalar codes cannot create that
-- identity.
------------------------------------------------------------------------

record EngineExecutionMissionSegmentWeld : Set where
  constructor engine-execution-mission-segment-weld
  field
    execution : Jet.JetEngineExecution
    segment : MissionSegment
    samePhysicalExecution : Bool
    samePhysicalExecutionIsTrue : samePhysicalExecution ≡ true
    installedConfigurationReference : String
    temporalAlignmentReference : String

open EngineExecutionMissionSegmentWeld public

data MatchingFuelCodeCreatesSameExecutionPermission : Set where

matchingFuelCodeDoesNotCreateSameExecution :
  MatchingFuelCodeCreatesSameExecutionPermission → ⊥
matchingFuelCodeDoesNotCreateSameExecution ()

------------------------------------------------------------------------
-- Fleet / demand lift.  This is the aviation analogue of the datacentre
-- demand-capacity-resource distinction: efficiency is an intensity coordinate,
-- while absolute resource use also depends on realised service demand.
------------------------------------------------------------------------

record FleetDemandScenario : Set where
  constructor fleet-demand-scenario
  field
    serviceDemandCode : Nat
    servicePerMissionCode : Nat
    missionsCode : Nat
    fuelPerMissionCode : Nat
    absoluteFuelCode : Nat
    sameScenario : Bool
    sameScenarioIsTrue : sameScenario ≡ true

open FleetDemandScenario public

data IntensityImprovementCreatesDemandTrajectoryPermission : Set where

intensityImprovementDoesNotCreateDemandTrajectory :
  IntensityImprovementCreatesDemandTrajectoryPermission → ⊥
intensityImprovementDoesNotCreateDemandTrajectory ()

------------------------------------------------------------------------
-- Reverse acquisition frontier.  The shortest empirical path is mission-first:
-- obtain a same-aircraft/configuration mission trajectory and its fuel carrier;
-- descend into maps/cycle/material models only when needed to explain, predict,
-- or counterfactually vary that trajectory.
------------------------------------------------------------------------

data MissionEnergyReverseTarget : Set where
  acquireMissionIdentity : MissionEnergyReverseTarget
  acquireAircraftEngineConfiguration : MissionEnergyReverseTarget
  acquireSegmentTimeline : MissionEnergyReverseTarget
  acquireSegmentFuelBurn : MissionEnergyReverseTarget
  acquireMissionFuelPathway : MissionEnergyReverseTarget
  acquireMissionEmissionInventory : MissionEnergyReverseTarget
  acquireNonCO2ForcingProducer : MissionEnergyReverseTarget
  acquireFleetDemandTrajectory : MissionEnergyReverseTarget

record MissionEnergyReverseObligation : Set where
  constructor mission-energy-reverse-obligation
  field
    target : MissionEnergyReverseTarget
    preferredEvidence : String
    promotes : String
    cannotPromote : String

open MissionEnergyReverseObligation public

record CanonicalMissionEnergyBoundary : Set where
  constructor canonical-mission-energy-boundary
  field
    detailedCycleModelMandatoryForEveryMissionPayment : Bool
    detailedCycleModelMandatoryForEveryMissionPaymentIsFalse :
      detailedCycleModelMandatoryForEveryMissionPayment ≡ false
    sameMissionCarrierMandatory : Bool
    sameMissionCarrierMandatoryIsTrue : sameMissionCarrierMandatory ≡ true
    efficiencyIntensityDistinctFromAbsoluteDemand : Bool
    efficiencyIntensityDistinctFromAbsoluteDemandIsTrue :
      efficiencyIntensityDistinctFromAbsoluteDemand ≡ true

canonicalMissionEnergyBoundary : CanonicalMissionEnergyBoundary
canonicalMissionEnergyBoundary =
  canonical-mission-energy-boundary false refl true refl true refl
