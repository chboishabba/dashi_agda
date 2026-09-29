{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974ThermomechanicalReconstructionExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Propulsion.RocketdyneBerylliumQualificationEvidenceExact as R
import DASHI.Physics.Propulsion.Rocketdyne1974MeasuredResultsExact as M

------------------------------------------------------------------------
-- Physics reconstruction, source-scoped, NASA-CR-140308 (1974)
-- R-9557 printed p.155, "Off-Limits Engine":
--    reported Haynes-25 USEFUL limit about 2200 F;
--    reported test-768 nozzle EQUILIBRIUM temperature 2300 F;
--    reported approximate melt temperature 2400 F.
-- Outcome: temperature-induced loss of strength and damaged nozzle extension.
-- These numbers are approximate in the SOURCE, even where the natural-number
-- encodings permit exact arithmetic on their published nominal values.
--
-- Executive Summary R-9557-1 p.6 rounds the same worst-case pressure to
-- 238 psia; R-9557 printed p.155 gives 237 psia. Keep the sources distinct.
------------------------------------------------------------------------

data Dimension : Set where
  force massRate velocity time acceleration area
    pressure temperature absoluteTemperature
    mass massDensity energyPerMass dimensionless : Dimension

data Quantity (d : Dimension) : Set where
  variable : String → Quantity d
  measured : Nat → Nat → String → Quantity d

-- A numerator and a positive, successor-form denominator keep zero-scale
-- encodings out of any newly admitted numeric observations.
record Scaled (d : Dimension) : Set where
  constructor scaled
  field
    numerator : Nat
    denominatorMinusOne : Nat
    unit : String
    sourceLocator : String

denominator : {d : Dimension} → Scaled d → Nat
denominator x = suc (Scaled.denominatorMinusOne x)

record MeasuredCondition : Set where
  constructor measured-condition
  field
    article : R.TestArticle
    experiment : String
    oxidizerToFuelRatio : Scaled dimensionless
    chamberPressure : Scaled pressure
    nozzleTemperature : Scaled temperature
    sourceLocator : String

-- One source-based extreme condition.  The ratio is stated as about 2.9
-- in the final-report narrative, so store 29/10 rather than presuming its
-- exact instrumental precision or silently merging the table's 2.88.
test768FinalReportNarrative : MeasuredCondition
test768FinalReportNarrative = measured-condition
  R.offLimitsEngine "test 768 / simulated dual oxidizer regulator malfunction"
  (scaled 29 9 "oxidizer/fuel mass ratio" "R-9557 p.155 (approximate)")
  (scaled 237 0 "psia" "R-9557 p.155")
  (scaled 2300 0 "degF" "R-9557 p.155 (thermal equilibrium)")
  "R-9557 p.155 off-limits engine narrative"

record SourcePrecisionDisagreement : Set where
  constructor source-precision-disagreement
  field
    finalReportValue : Nat
    executiveSummaryValue : Nat
    unit : String
    finalReportLocator : String
    summaryLocator : String

extremePressureSourceDisagreement : SourcePrecisionDisagreement
extremePressureSourceDisagreement =
  source-precision-disagreement 237 238 "psia"
    "R-9557 final report p.155"
    "R-9557-1 executive summary p.6"

-- Explicitly retain nominal source values in the *same* reported F unit.
haynes25UsefulLimitF : Nat
haynes25UsefulLimitF = 2200

test768NozzleF : Nat
test768NozzleF = 2300

haynes25ApproxMeltF : Nat
haynes25ApproxMeltF = 2400

record MeasuredTemperatureExceedsUsefulLimit : Set where
  constructor exceedance
  field
    usefulLimitF : Nat
    observedF : Nat
    excessF : Nat
    exactNominalDifference : usefulLimitF + excessF ≡ observedF
    sourceLocator : String

observedExceedsUsefulLimit : MeasuredTemperatureExceedsUsefulLimit
observedExceedsUsefulLimit = exceedance
  haynes25UsefulLimitF test768NozzleF 100 refl "R-9557 p.155"

record MeasuredTemperatureBelowApproxMelt : Set where
  constructor melt-margin
  field
    observedF : Nat
    approxMeltF : Nat
    remainingNominalF : Nat
    exactNominalDifference : observedF + remainingNominalF ≡ approxMeltF
    sourceLocator : String

observedBelowApproxMelt : MeasuredTemperatureBelowApproxMelt
observedBelowApproxMelt = melt-margin
  test768NozzleF haynes25ApproxMeltF 100 refl "R-9557 p.155"

-- This is the substantive source-matched physical conclusion: the observed
-- failure point can exceed the stated strength-related useful temperature
-- range while remaining BELOW the nominal melting temperature.  Material
-- *melting* is NOT an obligation or the asserted explanation of the event.
record StrengthLossWithoutMeltingComparison : Set where
  constructor strength-loss-comparison
  field
    exceedsServiceRange : MeasuredTemperatureExceedsUsefulLimit
    belowApproxMelt : MeasuredTemperatureBelowApproxMelt
    observedComponentOutcome : M.ComponentOutcome
    archive : String

test768StrengthLossComparison : StrengthLossWithoutMeltingComparison
test768StrengthLossComparison =
  strength-loss-comparison observedExceedsUsefulLimit
    observedBelowApproxMelt M.nozzleHighTemperatureDamage
    "NASA-CR-140308 p.155; reported loss of Haynes-25 strength"

------------------------------------------------------------------------
-- Equations are dimension-indexed *syntax*: their validity is a separate
-- empirical/model-calibration payment, not smuggled into an Agda postulate.
--
-- F = mdot * ve + (pe - pa) * Ae
-- Isp = F / (mdot * g0)
-- cstar = pc * At / mdot
-- Cf = F / (pc * At)
--
-- No numeric result follows without at least mdot, throat area, exit area,
-- nozzle pressure, back-pressure and measured thrust on the SAME operating
-- condition.  Ideal-gas gamma, gas constant, temperature, cooling profile,
-- nozzle efficiency and loss terms are additional model inputs.
------------------------------------------------------------------------

data PropulsionEquation : Set where
  thrustMomentumAndPressure : PropulsionEquation
  specificImpulse : PropulsionEquation
  characteristicVelocity : PropulsionEquation
  thrustCoefficient : PropulsionEquation
  chamberEnergyBalance : PropulsionEquation
  wallHeatBalance : PropulsionEquation
  temperatureDependentStrength : PropulsionEquation

record ModelParameter (d : Dimension) : Set where
  constructor model-parameter
  field
    physicalName : String
    value : Quantity d
    evidenceReference : String

record SameOperatingPoint : Set where
  constructor same-operating-point
  field
    runIdentifier : String
    measurementTime : String
    geometryRevision : String
    propellantRevision : String

record ThermodynamicInputs : Set where
  constructor thermo-inputs
  field
    condition : SameOperatingPoint
    massFlow : ModelParameter massRate
    exitVelocity : ModelParameter velocity
    exitPressure : ModelParameter pressure
    ambientPressure : ModelParameter pressure
    exitArea : ModelParameter area
    throatArea : ModelParameter area
    chamberPressure : ModelParameter pressure
    effectiveGravity : ModelParameter acceleration
    thrust : ModelParameter force
    flowCalibrationReference : String

record ThermodynamicInference : Set where
  constructor thermo-inference
  field
    source : ThermodynamicInputs
    equations : String
    residualsAndUncertainty : String
    validationWithIndependentRun : String

-- Input-debt ledger: presence of a record does NOT prove that measurements
-- exist.  This canonical case explicitly names missing primary data.
record MissingInputs : Set where
  constructor missing-inputs
  field
    testRun : String
    geometry : String
    flow : String
    thermochemistry : String
    energyBalance : String
    materialLaw : String
    stressLoads : String
    damageInspection : String

test768OpenInputs : MissingInputs
test768OpenInputs = missing-inputs
  "test 768, nozzle extension, R-9557 p.155"
  "throat/exit areas, extension thickness/shape, attachment geometry, revision"
  "same-point calibrated mdot, thrust, exit/static pressures, nozzle efficiency"
  "species, equilibrium/frozen combustion, gamma, cp, transport coefficients"
  "axial/time-resolved heat flux, wall conduction, film cooling, emissivity"
  "temperature-dependent Haynes-25 and coated C-103 allowable stress, creep, fatigue"
  "pressure/mounting/thermal stress, thermal gradients, boundary conditions"
  "fractography and time-resolved strain to identify onset and failure mode"

data ReconstructionLevel : Set where
  sourceDocumented conditionMatched derivedWithInputs validatedPrediction : ReconstructionLevel

record ReconstructionReceipt : Set where
  constructor reconstruction-receipt
  field
    level : ReconstructionLevel
    sourceObservation : MeasuredCondition
    temperatureComparison : StrengthLossWithoutMeltingComparison
    unclosedInputs : MissingInputs
    scopeBoundary : String

currentReceipt : ReconstructionReceipt
currentReceipt = reconstruction-receipt sourceDocumented
  test768FinalReportNarrative test768StrengthLossComparison test768OpenInputs
  "Nominal useful-limit exceedance is source-backed; not a quantitative prediction of stress/fatigue or C-103 survivability."
