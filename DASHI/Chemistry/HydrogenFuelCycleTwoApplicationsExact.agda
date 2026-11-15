module DASHI.Chemistry.HydrogenFuelCycleTwoApplicationsExact where

-- User-supplied interpretation, 2026-11-10:
-- (A) At hydrocarbon power stations, co-located solar electricity powers
-- water-derived H2 and CO2-to-hydrocarbon conversion. Carbon may be captured
-- from exhaust or air, displacing newly extracted fossil hydrocarbons.
-- (B) In user's description of an inventor's car demonstration, the
-- hydrogen assistance is powered by EXTERNALLY CHARGED BATTERIES.
-- Both cases involve an EXTERNAL energy source; the user did not claim
-- that the power plant or car manufactures energy.
-- These are interpretation/scope facts supplied by the user, NOT verified
-- quotations from a recovered transcript, measurements, or patent claims.
--
-- General chemistry/energy conservation belongs to conventional prior art.
-- Type-indexed SI and conservation machinery have existing DASHI owners;
-- this two-application adapter is user-directed and ChatGPT-drafted.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Physics.Units.SI as SI

data ExternalSupply : Set where
  solarElectricity : ExternalSupply
  offboardChargedBattery : ExternalSupply

data CarbonOrigin : Set where
  capturedPowerStationExhaust : CarbonOrigin
  capturedAtmosphericCO2 : CarbonOrigin

data Deployment : Set where
  hydrocarbonPowerStation : Deployment
  externallyChargedCar : Deployment

record PlantSynthesisScope : Set where
  field
    solarInput : SI.Measurement SI.Energy SI.unitScale
    co2Origin : CarbonOrigin
    waterInputMeasured : Set
    hydrogenFromWaterAccounted : Set
    capturedCarbonMeasured : Set
    regeneratedHydrocarbonIdentified : Set
    solarToHydrogenAndSynthesisTrace : Set
    captureAndAuxiliaryEnergyPaid : Set
    productAndStorageInventoryPaid : Set
    powerStationCombustionAndEmissionsPaid : Set

record CarEnrichmentScope : Set where
  field
    externallyChargedBatteryInput : SI.Measurement SI.Energy SI.unitScale
    batteryBeforeAndAfterSOCMeasured : Set
    waterToHydrogenConversionMeasured : Set
    addedOxygenAndHydrogenMeasured : Set
    dieselFuelAndUsefulWorkMatched : Set
    electricityAndAuxiliaryWorkPaid : Set

-- Solar synthesis and battery-assisted combustion are distinct uses.
-- No assertion that the car carries a CO2-to-hydrocarbon synthesis reactor.
data ApplicationRole : Deployment → Set where
  powerStationRegeneration :
    PlantSynthesisScope → ApplicationRole hydrocarbonPowerStation
  carHydrogenEnrichment :
    CarEnrichmentScope → ApplicationRole externallyChargedCar

-- Source-described carbon supply can be either station exhaust or DAC.
-- Carbon reuse and fossil-extraction displacement are conditional on actual
-- chemical output, source energy, material capture and lifecycle boundaries.
data CarbonIdentity : Set where
  recycledCapturedCarbon : CarbonIdentity
  newlyExtractedFossilCarbon : CarbonIdentity

recycledIsNotNewlyExtracted :
  recycledCapturedCarbon ≡ newlyExtractedFossilCarbon → ⊥
recycledIsNotNewlyExtracted ()

record SourceClaimAdmission : Set₁ where
  field
    actualSpeakerTranscriptLocator : Set
    sourceSpecificApparatusIdentity : Set
    sourceSpecificMeasurementAndCalibration : Set
    separatePowerStationAndCarClaims : Set
