{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974MeasuredResultsExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Propulsion.RocketdyneBerylliumQualificationEvidenceExact as R

-- NASA-CR-140308 / Rocketdyne R-9557 (Paster and French, Oct 1974).
-- Primary: https://ntrs.nasa.gov/citations/19740027091
-- PDF: https://ntrs.nasa.gov/api/citations/19740027091/downloads/19740027091.pdf
-- Units are lexical tags. Values are exact decimal encodings with an explicit
-- positive denominator; no assertion of measurement exactness/uncertainty.
-- An archived measurement is not a new mathematical derivation.

data ResultKind : Set where
  observed measuredDerived reportedDesignLimit reportedAnalysis : ResultKind

data Unit : Set where
  lbf second psia fahrenheit hz lbfSecond
  specificImpulseSeconds dimensionless : Unit

record DecimalResult : Set where
  constructor decimal-result
  field
    article : R.TestArticle
    quantity : String
    numerator : Nat
    scale : Nat
    unit : Unit
    kind : ResultKind
    condition : String
    locator : String

-- R-9557 report printed p.5 (SUMMARY), test condition matters.
saturatedIsp : DecimalResult
saturatedIsp = decimal-result R.durabilityEngine "steady specific impulse"
  2900 10 specificImpulseSeconds observed
  "nominal design point, helium-saturated propellants; nonoptimum nozzle contour"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

unsaturatedIsp : DecimalResult
unsaturatedIsp = decimal-result R.durabilityEngine "steady specific impulse"
  2944 10 specificImpulseSeconds observed
  "nominal design point, unsaturated propellants; nonoptimum nozzle contour"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

pulseIsp : DecimalResult
pulseIsp = decimal-result R.durabilityEngine "pulse specific impulse goal demonstrated"
  220 1 specificImpulseSeconds observed
  "helium-saturated propellants, 5 Hz, minimum impulse bit 30 lbf-s"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

minImpulseBit : DecimalResult
minImpulseBit = decimal-result R.durabilityEngine "minimum impulse bit"
  30 1 lbfSecond observed
  "5 Hz pulse demonstration, helium-saturated propellants"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

startTransient : DecimalResult
startTransient = decimal-result R.durabilityEngine "command to 90 percent response"
  40 1000 second observed
  "MOOG Inc. bipropellant valve; maximum pressure overshoot reported as 20 percent"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

shutdownTransient : DecimalResult
shutdownTransient = decimal-result R.durabilityEngine "off command to 10 percent chamber pressure"
  20 1000 second observed
  "tested shutdown transient"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

maxSingleBurn : DecimalResult
maxSingleBurn = decimal-result R.durabilityEngine "demonstrated single burn"
  600 1 second observed
  "steady-state performance and thermal equilibrium achieved"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

minimumPulseFrequency : DecimalResult
minimumPulseFrequency = decimal-result R.durabilityEngine "demonstrated pulse frequency lower bound"
  1 3 hz observed
  "pulse mission duty-cycle tests, 0.050 to 1.0 second pulse width"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

maximumPulseFrequency : DecimalResult
maximumPulseFrequency = decimal-result R.durabilityEngine "demonstrated pulse frequency upper bound"
  5 1 hz observed
  "pulse mission duty-cycle tests, 0.050 to 1.0 second pulse width"
  "R-9557 p.5 SUMMARY, DURABILITY ENGINE"

-- Table 39 is a separate off-limits engine; do NOT silently treat its
-- corrected Isp as uncorrected durability-engine nominal Isp.
record OffLimitsPoint : Set where
  constructor off-limits-point
  field
    testNumber : Nat
    mixtureRatioHundredths : Nat
    chamberPressureTenthsPsia : Nat
    characteristicVelocityFeetPerSec : Nat
    chamberTempF : Nat
    throatTempF : Nat
    nozzleTempF : Nat
    tableLocator : String

-- The first two entries of test 768 (November 6, 1973).
table39Nominal : OffLimitsPoint
table39Nominal = off-limits-point 768 165 2002 4954 337 511 1770
  "R-9557 printed p.156 Table 39, test 768, 200 s data point"

table39Extreme : OffLimitsPoint
table39Extreme = off-limits-point 768 288 2370 5001 352 601 2300
  "R-9557 printed p.156 Table 39, test 768, 10 s data point"

-- Exactly check elementary conversions/differences on integer encodings.
-- This is verified arithmetic ON the recorded numbers, not validation of
-- thermocouples, precision, causal explanations or extrapolation.
specificImpulseTenthsDifference :
  DecimalResult.numerator unsaturatedIsp ≡
  DecimalResult.numerator saturatedIsp + 44
specificImpulseTenthsDifference = refl

extremePressureDifferenceTenths :
  OffLimitsPoint.chamberPressureTenthsPsia table39Extreme ≡
  OffLimitsPoint.chamberPressureTenthsPsia table39Nominal + 368
extremePressureDifferenceTenths = refl

extremeNozzleTemperatureDifferenceF :
  OffLimitsPoint.nozzleTempF table39Extreme ≡
  OffLimitsPoint.nozzleTempF table39Nominal + 530
extremeNozzleTemperatureDifferenceF = refl

startTransientTwiceShutdown :
  DecimalResult.numerator startTransient ≡
  2 * DecimalResult.numerator shutdownTransient
startTransientTwiceShutdown = refl

-- Failure is a component-specific finding, not a universal pressure
-- threshold; the off-limits engine continued after a nozzle modification.
data Component : Set where
  berylliumCombustor moogBipropellantValve haynes25Nozzle
  brazeJoint niobiumNozzle : Component

data Outcome : Set where
  passedScope superficialDamage detrimentalDamage modifiedAndRetested : Outcome

record ComponentOutcome : Set where
  constructor component-outcome
  field
    article : R.TestArticle
    component : Component
    outcome : Outcome
    context : String
    sourceLocator : String

nozzleHighTemperatureDamage : ComponentOutcome
nozzleHighTemperatureDamage = component-outcome
  R.offLimitsEngine haynes25Nozzle detrimentalDamage
  "test 768 extreme oxidizer-rich condition; 2300 F nozzle temperature; local strength loss, not a standalone pressure-failure threshold"
  "R-9557 p.156 Table 39; R-9557-1 Executive Summary p.26"

moogContamination : ComponentOutcome
moogContamination = component-outcome
  R.durabilityEngine moogBipropellantValve detrimentalDamage
  "sand/dust migration into poppet/seat during vibration; reported excessive leakage; valve substituted for later test"
  "R-9557-1 Executive Summary pp.5, 26"

berylliumSurface : ComponentOutcome
berylliumSurface = component-outcome
  R.durabilityEngine berylliumCombustor superficialDamage
  "six environmental cycles; superficial staining/pitting"
  "R-9557-1 Executive Summary p.5"

-- The original programme explicitly differentiated random-vibration
-- equivalent missions from actual flown missions.
record Campaign : Set where
  constructor campaign
  field
    historicalObservation : R.Observation
    simulatedMissionEquivalentCount : Nat
    flightDemonstrationCountClaimed : Nat
    sourceLocator : String

brazeJointQualification : Campaign
brazeJointQualification = campaign R.brazeVibration 100 0
  "R-9557 abstract and vibration simulator report; X/Y/Z random vibration"

-- Compare independent source revision: the Executive Summary has its own
-- NTRS accession (19740027092). Do not merge it with the final report.
executiveSummaryIdentifier : String
executiveSummaryIdentifier = "NASA NTRS 19740027092; R-9557-1"
