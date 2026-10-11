{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974ThermalModelValidationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-REPORTED THERMAL MODEL VALIDATION
--
-- NASA-CR-140308 / R-9557 reports that Durability Engine thermal predictions
-- were compared with measured baseline temperatures from test 052 on the
-- predicted isotherm and temperature-history plots (Figs. 91 and 92), and that
-- this correlation was then used for a chamber-weight-reduction analysis.
-- R-9557-1 separately reports about 200 s to steady-state temperature.
--
-- This is evidence that Rocketdyne had a source-validated thermal model.  It is
-- NOT a reconstructed model in DASHI: equations, mesh/network, local nozzle
-- wall gauge and the complete numerical temperature field are still unpaid.
------------------------------------------------------------------------

record ThermalValidationReceipt : Set where
  constructor thermal-validation-receipt
  field
    testIdentifier : String
    predictionObject : String
    measuredObject : String
    reportedAgreement : Bool
    reusedForDesignUpdate : Bool
    exactNumericalResidualRecovered : Bool
    sourceReference : String

open ThermalValidationReceipt public

test052ThermalValidation : ThermalValidationReceipt
test052ThermalValidation =
  thermal-validation-receipt
    "Durability Engine baseline performance test 052"
    "predicted isotherm + temperature-history plots, Figs. 91-92"
    "measured baseline engine temperatures plotted on the predictions"
    true true false
    "NASA-CR-140308 R-9557 p.175; R-9557-1 design-analysis section"

sourceValidatedThermalModelExists : Bool
sourceValidatedThermalModelExists = reportedAgreement test052ThermalValidation

steadyStateTimeSeconds : Nat
steadyStateTimeSeconds = 200

record SourceThermalCoordinates : Set where
  constructor source-thermal-coordinates
  field
    steadyStateApproxSeconds : Nat
    massAverageBerylliumTemperatureF : Nat
    analyzedMaximumBerylliumTemperatureF : Nat
    oxidationThresholdF : Nat
    erosionThresholdF : Nat
    sourceReference : String

sourceThermalCoordinates : SourceThermalCoordinates
sourceThermalCoordinates =
  source-thermal-coordinates
    200 435 1465 1800 2300
    "R-9557-1 pp.15-16; nominal/off-limits/streak-heating analysis"

record StructuralDesignCriteria : Set where
  constructor structural-design-criteria
  field
    minimumYieldSafetyFactorTenths : Nat
    minimumUltimateSafetyFactorTenths : Nat
    fatigueSafetyFactor : Nat
    axialInertiaG : Nat
    nozzleLateralInertiaG : Nat
    combustorNozzleLateralInertiaG : Nat
    sourceReference : String

structuralCriteria : StructuralDesignCriteria
structuralCriteria =
  structural-design-criteria
    12 20 10 360 143 100
    "NASA-CR-140308 R-9557 p.57; R-9557-1 p.16"

record ThermalModelBoundary : Set where
  constructor thermal-model-boundary
  field
    historicalModelWasComparedToTest : Bool
    completeHistoricalEquationsRecovered : Bool
    completeTest052TemperatureArrayRecovered : Bool
    localNozzleWallGaugeRecovered : Bool
    localHeatFluxFieldRecovered : Bool
    thermalModelDoesNotIdentifyNozzleStress : Bool
    historicalAgreementMayCalibrateFutureReconstruction : Bool

canonicalThermalModelBoundary : ThermalModelBoundary
canonicalThermalModelBoundary =
  thermal-model-boundary true false false false false true true

thermalModelDoesNotIdentifyNozzleStress : Bool
thermalModelDoesNotIdentifyNozzleStress =
  ThermalModelBoundary.thermalModelDoesNotIdentifyNozzleStress canonicalThermalModelBoundary
