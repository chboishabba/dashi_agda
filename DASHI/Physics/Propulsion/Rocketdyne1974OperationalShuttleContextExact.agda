{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974OperationalShuttleContextExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data RequirementKind : Set where
  faultTolerance calendarLife reuseCount operatingEnvironment : RequirementKind

record OrbiterRequirement : Set where
  constructor orbiter-requirement
  field
    kind : RequirementKind
    statement : String
    sourceReference : String

failOperationalFailSafe : OrbiterRequirement
failOperationalFailSafe = orbiter-requirement faultTolerance
  "fail-operational / fail-safe design drove redundant hardware and redundancy-management complexity"
  "NASA 1985 Design Evolution of the Orbiter RCS"

tenYearLife : OrbiterRequirement
tenYearLife = orbiter-requirement calendarLife "10-year life requirement"
  "NASA 1985 Design Evolution of the Orbiter RCS"

hundredMissionReuse : OrbiterRequirement
hundredMissionReuse = orbiter-requirement reuseCount "100-mission reuse capability"
  "NASA 1985 Design Evolution of the Orbiter RCS"

orbitAndReentry : OrbiterRequirement
orbitAndReentry = orbiter-requirement operatingEnvironment
  "RCS operation required both on orbit and during reentry"
  "NASA 1985 Design Evolution of the Orbiter RCS"

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
orbiterRCSChallengeSet = orbiter-rcs-challenge-set
  failOperationalFailSafe tenYearLife hundredMissionReuse orbitAndReentry
  true true true true
  "NASA 1985 Design Evolution of the Orbiter RCS"

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
operationalRCSArchitecture = operational-architecture
  "MMH / N2O4" 38 870 6 25
  "three removable modules: one forward and two aft"
  "AIAA 75-1299 / NTRS 19750061613"

------------------------------------------------------------------------
-- FLIGHT SUPPLIER / ARTICLE IDENTITY
------------------------------------------------------------------------

record OperationalFlightThrusterIdentity : Set where
  constructor operational-flight-thruster-identity
  field
    supplier : String
    familyName : String
    primaryNominalThrustLbf : Nat
    primaryNominalChamberPressurePsia : Nat
    primaryConstruction : String
    missionLife : Nat
    supplierIdentityPaid : Bool
    sameAsRocketdyneR9557Article : Bool
    sourceReference : String

marquardtR40AFlightIdentity : OperationalFlightThrusterIdentity
marquardtR40AFlightIdentity = operational-flight-thruster-identity
  "The Marquardt Company, Van Nuys, California"
  "R-40A / Shuttle primary RCS thruster lineage"
  870 152
  "coated columbium/C-103 chamber and nozzle; titanium also identified in Shuttle RCS parameter summary"
  100
  true false
  "NASA Space Transportation symposium RCS primary/vernier table (NTRS 19910018879); NASA design study NTRS 19790006961"

operationalPrimarySupplierPaid : Bool
operationalPrimarySupplierPaid = true

record TechnologyToFlightBoundary : Set where
  constructor technology-to-flight-boundary
  field
    rocketdyneProgrammeNominalThrustLbf : Nat
    operationalPrimaryNominalThrustLbf : Nat
    commonPropellantFamily : Bool
    commonReuseRequirementFamily : Bool
    sameNominalThrust : Bool
    sameFlightHardwareIdentityEstablished : Bool
    operationalSupplierIdentityEstablished : Bool
    technologyResultMayInformRequirementFeasibility : Bool
    technologyResultProvesFlightSelection : Bool
    boundary : String

rocketdyneTechnologyNotFlightIdentity : TechnologyToFlightBoundary
rocketdyneTechnologyNotFlightIdentity = technology-to-flight-boundary
  600 870 true true false false true true false
  "The eventual operational supplier/article family can be identified as Marquardt while the historical influence/procurement path from Rocketdyne R-9557 remains unproved. Supplier identification does not turn the 600-lbf Rocketdyne technology demonstrator into the 870-lbf flight thruster."

record OperationalContextBoundary : Set where
  constructor operational-context-boundary
  field
    shuttleRequirementContextRecovered : Bool
    laterOperationalArchitectureRecovered : Bool
    rocketdyneFlightSelectionReceiptRecovered : Bool
    finalManufacturerIdentityRecoveredHere : Bool
    directRocketdyneToMarquardtTechnologyTransferRecovered : Bool
    programmeChallengeTransferAllowed : Bool
    directHardwareIdentityAllowed : Bool
    nextHistoricalAcquisition : String

operationalContextBoundary : OperationalContextBoundary
operationalContextBoundary = operational-context-boundary
  true true false true false true false
  "Flight supplier identity is paid. Next acquire NASA source-selection/procurement/design-review records if the historical question is whether or how Rocketdyne INTEREGEN work influenced the selected Marquardt Shuttle RCS hardware."
