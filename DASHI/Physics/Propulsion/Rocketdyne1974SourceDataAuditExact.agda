{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974SourceDataAuditExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Propulsion.RocketdyneBerylliumQualificationEvidenceExact as R
import DASHI.Physics.Propulsion.Rocketdyne1974ThermomechanicalReconstructionExact as T

------------------------------------------------------------------------
-- Provenance-aware data audit: two distinct NASA reports, two strata.
-- Final report: R-9557 / NASA-CR-140308 / NTRS 19740027091.
-- Executive summary: R-9557-1 / NASA-CR-140309 / NTRS 19740027092.
-- Do not collapse requirements, demonstration data, or source rounding.
------------------------------------------------------------------------

data EvidenceStatus : Set where
  designRequirement demonstratedOperation narrativeApproximation
  simulatorQualification companionReportDescription : EvidenceStatus

data PhysicalUnit : Set where
  Fahrenheit psia psig seconds count lbf dimensionless
  lbfSecond perMission inCubed : PhysicalUnit

record IndexedScalar : Set where
  constructor indexed
  field
    sourceDocument : String
    reportPage : String
    article : R.TestArticle
    quantityName : String
    valueNumerator : Nat
    valueDenominator : Nat
    unit : PhysicalUnit
    status : EvidenceStatus
    conditions : String
    limitingCaveat : String

-- All denominators used here are literal positive units.
offLimitsStarts : IndexedScalar
offLimitsStarts = indexed "R-9557" "printed p.155" R.offLimitsEngine
  "hot-fire starts" 18 1 count demonstratedOperation
  "off-limits altitude campaign" "test article is NOT durability engine"

offLimitsTotalBurn : IndexedScalar
offLimitsTotalBurn = indexed "R-9557" "printed p.155" R.offLimitsEngine
  "cumulative burn duration" 2615 1 seconds demonstratedOperation
  "18 starts; mixed operating conditions" "not a single continuous firing"

extremeOffLimitsPressureFinal : IndexedScalar
extremeOffLimitsPressureFinal = indexed "R-9557" "printed p.155" R.offLimitsEngine
  "chamber pressure in worst-case narrative" 237 1 psia narrativeApproximation
  "test 768; approximately 2.9 oxidizer/fuel" "executive summary rounds to 238 psia"

extremeOffLimitsPressureSummary : IndexedScalar
extremeOffLimitsPressureSummary = indexed "R-9557-1" "printed p.6" R.offLimitsEngine
  "chamber pressure in worst-case summary" 238 1 psia narrativeApproximation
  "same worst-case programme" "do not substitute for final-report number"

haynes25UsefulTemperature : IndexedScalar
haynes25UsefulTemperature = indexed "R-9557" "printed p.155" R.offLimitsEngine
  "Haynes 25 approximate useful temperature limit" 2200 1 Fahrenheit
  narrativeApproximation "nozzle extension, hot operation"
  "NOT a measured temperature-dependent constitutive strength curve"

haynes25Test768NozzleTemperature : IndexedScalar
haynes25Test768NozzleTemperature = indexed "R-9557" "printed p.155" R.offLimitsEngine
  "test 768 equilibrium nozzle temperature" 2300 1 Fahrenheit
  demonstratedOperation "high mixture ratio and chamber pressure"
  "NOT a measured local stress or fracture threshold"

haynes25ApproximateMelting : IndexedScalar
haynes25ApproximateMelting = indexed "R-9557" "printed p.155" R.offLimitsEngine
  "Haynes 25 approximate melting point" 2400 1 Fahrenheit
  narrativeApproximation "material comparison" "material melting not reported as the failure mode"

niobiumFollowup : IndexedScalar
niobiumFollowup = indexed "R-9557" "printed p.155" R.offLimitsEngine
  "company-sponsored columbium nozzle follow-up run" 45 1 seconds
  demonstratedOperation "same extreme condition, separate company programme"
  "not a service-life qualification; downstream inspection/stress unknown"

initialEquilibriumFiring : IndexedScalar
initialEquilibriumFiring = indexed "R-9557" "printed p.155" R.offLimitsEngine
  "pre-excursion baseline firing" 200 1 seconds
  demonstratedOperation "before servo-driven transition to 2.9 mixture ratio"
  "not identical to subsequent 10-second excursion"

vibrationSimulatedMissions : IndexedScalar
vibrationSimulatedMissions = indexed "R-9557-1" "printed p.6" R.vibrationSimulator
  "equivalent random-vibration missions" 100 1 perMission
  simulatorQualification "three axes random vibration"
  "equivalent qualification profile, NOT 100 flights"

vibrationProofPressure : IndexedScalar
vibrationProofPressure = indexed "R-9557-1" "printed p.6" R.vibrationSimulator
  "post-vibration structural proof pressure" 500 1 psig
  companionReportDescription "reported source unit 500 psig (GAUGE)"
  "do NOT substitute as absolute psia"

-- Fix pressure-unit semantics via an explicit separate typed axis.
data PressureReference : Set where
  absolute gauge : PressureReference

record PressureMeasurement : Set where
  constructor pressure-measurement
  field
    pressureHundredthsPsi : Nat
    reference : PressureReference
    testArticle : R.TestArticle
    sourcePage : String

simulatorProofGauge : PressureMeasurement
simulatorProofGauge = pressure-measurement 50000 gauge R.vibrationSimulator
  "R-9557-1 p.6 posttest structural proof 500 psig"

simulatorLeakTestGauge : PressureMeasurement
simulatorLeakTestGauge = pressure-measurement 20000 gauge R.vibrationSimulator
  "R-9557-1 p.6 posttest leak 200 psig"

test768ChamberAbsolute : PressureMeasurement
test768ChamberAbsolute = pressure-measurement 23700 absolute R.offLimitsEngine
  "R-9557 p.155 237 psia"

-- A separate unit constructor prevents data export from treating psig as
-- psia merely because both are PSI.
differentReferenceIsNotConversion : PressureReference
differentReferenceIsNotConversion = gauge

-- Source-level, not physics-level: these formal identities concern exact
-- encodings of the printed nominal numbers only.
test768TemperatureNominalDifference :
  2200 + 100 ≡ 2300
test768TemperatureNominalDifference = refl

test768BelowApproxMelt :
  2300 + 100 ≡ 2400
test768BelowApproxMelt = refl

-- Design specifications sourced to R-9557-1 Table 1 p.8; do not confuse
-- with empirical achieved endpoints or with lifetime validation.
data ProgrammeRequirement : Set where
  targetMissionLife targetYears targetBurnTime targetTotalPulses : ProgrammeRequirement

record DesignSpecification : Set where
  constructor design-specification
  field
    parameter : ProgrammeRequirement
    number : Nat
    unitDescription : String
    source : String

designLifeInMissions : DesignSpecification
designLifeInMissions = design-specification targetMissionLife 100 "missions"
  "R-9557-1 p.8 Table 1 (design requirement)"

designLifeInYears : DesignSpecification
designLifeInYears = design-specification targetYears 10 "years"
  "R-9557-1 p.8 Table 1 (design requirement)"

designLifeBurn : DesignSpecification
designLifeBurn = design-specification targetBurnTime 100000 "seconds"
  "R-9557-1 p.8 Table 1 (design requirement)"

designLifePulses : DesignSpecification
designLifePulses = design-specification targetTotalPulses 200000 "pulses"
  "R-9557-1 p.8 Table 1 (design requirement)"

-- Never infer that qualification test duration equals a demonstrated
-- 100,000 s lifetime; these constructor types remain disjoint.
