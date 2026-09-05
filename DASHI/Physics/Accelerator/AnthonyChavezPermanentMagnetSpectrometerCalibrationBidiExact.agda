module DASHI.Physics.Accelerator.AnthonyChavezPermanentMagnetSpectrometerCalibrationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.InverseProblemIdentifiabilityBidiExact as Inv

------------------------------------------------------------------------
-- Burris-Mog, Mark Anthony Chavez, Espy, Moir, Schillig, Volegov, Manard,
-- Trainham, Review of Scientific Instruments 89, 073303 (2018),
-- DOI 10.1063/1.5029837.
--
-- The work calibrates two compact permanent-magnet spectrometers for high-
-- current electron linear induction accelerators, including DARHT use.
------------------------------------------------------------------------

data SpectrometerCoordinate : Set where
  magneticFieldMap entranceGeometry detectorPosition electronEnergy : SpectrometerCoordinate

record PermanentMagnetSpectrometer : Set where
  constructor permanent-magnet-spectrometer
  field
    fieldMapReceipt : String
    geometryReceipt : String
    detectorReceipt : String
    calibrationReference : String

open PermanentMagnetSpectrometer public

record EnergyInferencePath : Set where
  constructor energy-inference-path
  field
    rawDetectorCoordinate : String
    calibratedTrajectoryCoordinate : String
    inferredElectronEnergy : String
    fieldAndGeometryRequired : Bool
    fieldAndGeometryRequiredIsTrue : fieldAndGeometryRequired ≡ true
    sourceReference : String

open EnergyInferencePath public

record SpectrometerCalibrationBoundary : Set where
  constructor spectrometer-calibration-boundary
  field
    detectorPositionIsElectronEnergyByDefinition : Bool
    detectorPositionIsElectronEnergyByDefinitionIsFalse :
      detectorPositionIsElectronEnergyByDefinition ≡ false
    nominalMagnetStrengthAloneClosesCalibration : Bool
    nominalMagnetStrengthAloneClosesCalibrationIsFalse :
      nominalMagnetStrengthAloneClosesCalibration ≡ false
    calibratedMappingNeedsFieldAndGeometryModel : Bool
    calibratedMappingNeedsFieldAndGeometryModelIsTrue :
      calibratedMappingNeedsFieldAndGeometryModel ≡ true
    calibrationAtOneConfigurationAutomaticallyTransfersToAllConfigurations : Bool
    calibrationAtOneConfigurationAutomaticallyTransfersToAllConfigurationsIsFalse :
      calibrationAtOneConfigurationAutomaticallyTransfersToAllConfigurations ≡ false

canonicalSpectrometerCalibrationBoundary : SpectrometerCalibrationBoundary
canonicalSpectrometerCalibrationBoundary =
  spectrometer-calibration-boundary false refl false refl true refl false refl

chavezSpectrometerReverse : Inv.InverseProblemReverseObligation
chavezSpectrometerReverse = Inv.inverse-problem-reverse-obligation
  "compact permanent-magnet electron spectrometer"
  "electron kinetic-energy distribution"
  "detector impact/position coordinate"
  "field-map, detector, geometry and reference-beam calibration"
  "charged-particle trajectory through measured permanent-magnet field"
  "different field/geometry errors can mimic energy shifts"
  "independent reference-energy or second spectrometer configuration"
