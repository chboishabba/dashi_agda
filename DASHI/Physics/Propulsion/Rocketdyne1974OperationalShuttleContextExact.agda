{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974OperationalShuttleContextExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- OPERATIONAL SHUTTLE RCS CONTEXT
--
-- This owner prevents a common historical promotion error:
-- a technology contract demonstrating compatibility with Shuttle RCS
-- requirements is not thereby the flight RCS hardware.
--
-- Sources:
--   * NASA 1985 "Design Evolution of the Orbiter Reaction Control Subsystem"
--     (NTRS 19850008635)
--   * AIAA 75-1299 / NTRS 19750061613, operational RCS description
--   * NASA-CR-140308 / R-9557, Rocketdyne technology programme
------------------------------------------------------------------------

data RequirementKind : Set where
  faultTolerance calendarLife reuseCount operatingEnvironment : RequirementKind

record OrbiterRequirement : Set where
  constructor orbiter-requirement
  field
    kind : RequirementKind
    statement : String
    sourceReference : String

failOperationalFailSafe : OrbiterRequirement
failOperationalFailSafe =
  orbiter-requirement faultTolerance
    "fail-operational / fail-safe design drove redundant hardware and redundancy-management complexity"
    "NASA 1985 Design Evolution of the Orbiter RCS, introduction"

tenYearLife : OrbiterRequirement
tenYearLife =
  orbiter-requirement calendarLife
    "10-year life requirement"
    "NASA 1985 Design Evolution of the Orbiter RCS, introduction"

hundredMissionReuse : OrbiterRequirement
hundredMissionReuse =
  orbiter-requirement reuseCount
    "100-mission reuse capability"
    "NASA 1985 Design Evolution of the Orbiter RCS, introduction"

orbitAndReentry : OrbiterRequirement
orbitAndReentry =
  orbiter-requirement operatingEnvironment
    "RCS operation required both on orbit and during reentry"
    "NASA 1985 Design Evolution of the Orbiter RCS, introduction"

record OrbiterRCSChallengeSet : Set where
  constructor orbiter-rcs-challenge-set
  field
    faultToleranceRequirement : OrbiterRequirement
    lifeRequirement : OrbiterRequirement
    reuseRequirement : OrbiterRequirement
    environmentRequirement : OrbiterRequirement
    materialCompatibilityChallenge : Bool
    groundTurnaroundChallenge : Bool
    wearoutChallenge : Bool
    verificationByAnalysisAndTest : Bool
    sourceReference : String

orbiterRCSChallengeSet : OrbiterRCSChallengeSet
orbiterRCSChallengeSet =
  orbiter-rcs-challenge-set
    failOperationalFailSafe tenYearLife hundredMissionReuse orbitAndReentry
    true true true true
    "NASA 1985 Design Evolution of the Orbiter RCS: long life/reuse drove material selection, compatibility, ground handling/turnaround and wearout problems"

record OperationalArchitecture : Set where
  constructor operational-architecture
  field
    propellants : String
    primaryThrusterCount : Nat
    primaryThrustLbf : Nat
    vernierThrusterCount : Nat
    vernierThrustLbf : Nat
    moduleArchitecture : String
    sourceReference : String

operationalRCSArchitecture : OperationalArchitecture
operationalRCSArchitecture =
  operational-architecture
    "MMH / N2O4"
    38 870
    6 25
    "three removable modules: one forward and two aft; architecture chosen to support maintenance/turnaround and mission flexibility"
    "AIAA 75-1299 / NTRS 19750061613"

record TechnologyToFlightBoundary : Set where
  constructor technology-to-flight-boundary
  field
    rocketdyneProgrammeNominalThrustLbf : Nat
    operationalPrimaryNominalThrustLbf : Nat
    commonPropellantFamily : Bool
    commonReuseRequirementFamily : Bool
    sameNominalThrust : Bool
    sameFlightHardwareIdentityEstablished : Bool
    technologyResultMayInformRequirementFeasibility : Bool
    technologyResultProvesFlightSelection : Bool
    boundary : String

rocketdyneTechnologyNotFlightIdentity : TechnologyToFlightBoundary
rocketdyneTechnologyNotFlightIdentity =
  technology-to-flight-boundary
    600 870
    true true false false true false
    "R-9557 is evidence that a 600-lbf beryllium INTEREGEN concept could satisfy tested Shuttle-RCS-style requirements; later operational RCS descriptions use 870-lbf primary thrusters. Do not identify the technology demonstrator with flight hardware without a procurement/selection/same-object receipt."

record OperationalContextBoundary : Set where
  constructor operational-context-boundary
  field
    shuttleRequirementContextRecovered : Bool
    laterOperationalArchitectureRecovered : Bool
    rocketdyneFlightSelectionReceiptRecovered : Bool
    finalManufacturerIdentityRecoveredHere : Bool
    programmeChallengeTransferAllowed : Bool
    directHardwareIdentityAllowed : Bool
    nextHistoricalAcquisition : String

operationalContextBoundary : OperationalContextBoundary
operationalContextBoundary =
  operational-context-boundary
    true true false false true false
    "Acquire NASA source-selection/procurement records and primary-engine design-evolution records if the historical question is whether/how the Rocketdyne technology programme influenced the eventual Orbiter RCS hardware."
