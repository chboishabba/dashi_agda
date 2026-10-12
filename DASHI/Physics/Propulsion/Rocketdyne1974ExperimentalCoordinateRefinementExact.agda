{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974ExperimentalCoordinateRefinementExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coord

data RunWorld : Set where
  haynes768 wc1038702 : RunWorld

data RunControl : Set where
  replayHistoricalObservation : RunControl

data RunDimension : Set where
  temperatureF materialCode geometricCode boundaryCode processCode : RunDimension

data RunCoordinate : Set where
  equilibriumNozzleTemperature nozzleMaterial nozzleCoating
  localWallGauge localConstraintState manufacturingProcessHistory : RunCoordinate

readCoordinate : RunCoordinate → RunWorld → Nat
readCoordinate equilibriumNozzleTemperature haynes768 = 2300
readCoordinate equilibriumNozzleTemperature wc1038702 = 2300
readCoordinate nozzleMaterial haynes768 = 25
readCoordinate nozzleMaterial wc1038702 = 103
readCoordinate nozzleCoating haynes768 = 0
readCoordinate nozzleCoating wc1038702 = 101
readCoordinate localWallGauge haynes768 = 0
readCoordinate localWallGauge wc1038702 = 0
readCoordinate localConstraintState haynes768 = 0
readCoordinate localConstraintState wc1038702 = 0
-- Zero here is an explicit unrecovered historical code, not an assertion that
-- the two manufacturing routes were identical.
readCoordinate manufacturingProcessHistory haynes768 = 0
readCoordinate manufacturingProcessHistory wc1038702 = 0

coordinateRole : RunCoordinate → Coord.CoordinateRole
coordinateRole equilibriumNozzleTemperature = Coord.measuredObservable
coordinateRole nozzleMaterial = Coord.measuredObservable
coordinateRole nozzleCoating = Coord.measuredObservable
coordinateRole localWallGauge = Coord.nuisanceCoordinate
coordinateRole localConstraintState = Coord.nuisanceCoordinate
coordinateRole manufacturingProcessHistory = Coord.nuisanceCoordinate

coordinateDimension : RunCoordinate → RunDimension
coordinateDimension equilibriumNozzleTemperature = temperatureF
coordinateDimension nozzleMaterial = materialCode
coordinateDimension nozzleCoating = materialCode
coordinateDimension localWallGauge = geometricCode
coordinateDimension localConstraintState = boundaryCode
coordinateDimension manufacturingProcessHistory = processCode

applyHistoricalControl : RunControl → RunWorld → RunWorld
applyHistoricalControl replayHistoricalObservation w = w

coordinateReference : RunCoordinate → String
coordinateReference equilibriumNozzleTemperature = "NASA-CR-140308 Tests 768 and 870-2: about 2300 F equilibrium nozzle temperature"
coordinateReference nozzleMaterial = "NASA-CR-140308: Haynes-25 versus WC103 columbium"
coordinateReference nozzleCoating = "NASA-CR-140308: WC103 nozzle identified with Vac Hyd VH-101 silicide coating"
coordinateReference localWallGauge = "engineering drawing / local wall-thickness acquisition still required"
coordinateReference localConstraintState = "mounting, support and thermo-mechanical constraint acquisition still required"
coordinateReference manufacturingProcessHistory = "1974 article fabrication traveler, surface treatment, braze/weld/coating history and inspection disposition still required"

dimensionReference : RunCoordinate → String
dimensionReference equilibriumNozzleTemperature = "degF"
dimensionReference nozzleMaterial = "categorical material code"
dimensionReference nozzleCoating = "categorical coating code"
dimensionReference localWallGauge = "length"
dimensionReference localConstraintState = "boundary-condition category"
dimensionReference manufacturingProcessHistory = "categorical process-history code"

calibrationReference : RunCoordinate → String
calibrationReference equilibriumNozzleTemperature = "R-9557 thermocouple / equilibrium-temperature report"
calibrationReference nozzleMaterial = "R-9557 hardware identity"
calibrationReference nozzleCoating = "R-9557 hardware/coating identity"
calibrationReference localWallGauge = "unpaid"
calibrationReference localConstraintState = "unpaid"
calibrationReference manufacturingProcessHistory = "unpaid; later Shuttle C-103 cracking demonstrates methodological relevance but does not identify the 1974 route"

controlReference : RunControl → String
controlReference replayHistoricalObservation = "historical replay only; no newly performed intervention asserted"

rocketdyneExperimentDesign : Coord.ExperimentalCoordinateDesign RunWorld RunControl Nat RunDimension
rocketdyneExperimentDesign = Coord.experimentalCoordinateDesign RunCoordinate coordinateRole coordinateDimension readCoordinate applyHistoricalControl coordinateReference dimensionReference calibrationReference controlReference

temperatureObservation : RunWorld → Nat
temperatureObservation w = Coord.read rocketdyneExperimentDesign equilibriumNozzleTemperature w

temperatureCollision : temperatureObservation haynes768 ≡ temperatureObservation wc1038702
temperatureCollision = refl

materialCodeDifference :
  Coord.read rocketdyneExperimentDesign nozzleMaterial haynes768 ≡
  Coord.read rocketdyneExperimentDesign nozzleMaterial wc1038702 → ⊥
materialCodeDifference ()

materialSeparatesTemperatureCollision : Coord.CoordinateSeparatesCollision rocketdyneExperimentDesign temperatureObservation
materialSeparatesTemperatureCollision = Coord.coordinateSeparatesCollision nozzleMaterial haynes768 wc1038702 refl materialCodeDifference

manufacturingProcessCoordinateOpen : Bool
manufacturingProcessCoordinateOpen = true

record CoordinateAcquisitionFrontier : Set where
  constructor coordinate-acquisition-frontier
  field
    temperatureCollisionPaid : Bool
    materialCoordinateSeparatesPaid : Bool
    coatingCoordinateDocumented : Bool
    localWallGaugeMeasured : Bool
    localConstraintStateMeasured : Bool
    manufacturingProcessHistoryMeasured : Bool
    completeHeatFluxFieldMeasured : Bool
    materialIsUniqueCauseEstablished : Bool
    nextBestAcquisition : String

nextCoordinateAcquisitionFrontier : CoordinateAcquisitionFrontier
nextCoordinateAcquisitionFrontier = coordinate-acquisition-frontier
  true true true false false false false false
  "Recover local wall gauge/profile + constraint state + 1974 manufacturing/process/inspection history + same-run heat-flux/temperature history; these coordinates can further refine the still-collapsed thermo-structural fibre."
