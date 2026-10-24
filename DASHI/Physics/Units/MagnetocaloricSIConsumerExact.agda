module DASHI.Physics.Units.MagnetocaloricSIConsumerExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Int using (pos)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial as MCE

------------------------------------------------------------------------
-- Magnetocaloric / AMR SI consumer.
--
-- Important distinction: tesla measures magnetic flux density B.  Magnetic
-- field strength H has coherent SI unit A m^-1.  They are kept at different
-- dimensions here so an engineering calibration cannot silently substitute
-- one for the other.
------------------------------------------------------------------------

MagneticFieldStrength Entropy HeatCapacity SpecificHeatCapacity ThermalConductivity : SI.Dimension
MagneticFieldStrength =
  SI.dim SI.minusOne SI.zeroI SI.zeroI SI.one SI.zeroI SI.zeroI SI.zeroI
Entropy =
  SI.dim (pos 2) SI.one SI.minusTwo SI.zeroI SI.minusOne SI.zeroI SI.zeroI
HeatCapacity = Entropy
SpecificHeatCapacity =
  SI.dim (pos 2) SI.zeroI SI.minusTwo SI.zeroI SI.minusOne SI.zeroI SI.zeroI
ThermalConductivity =
  SI.dim SI.one SI.one SI.minusThree SI.zeroI SI.minusOne SI.zeroI SI.zeroI

amperePerMetre : SI.Unit MagneticFieldStrength
amperePerMetre = SI.mkUnit "A m⁻¹" "ampere per metre"

joulePerKelvin : SI.Unit Entropy
joulePerKelvin = SI.mkUnit "J K⁻¹" "joule per kelvin"

joulePerKilogramKelvin : SI.Unit SpecificHeatCapacity
joulePerKilogramKelvin = SI.mkUnit "J kg⁻¹ K⁻¹" "joule per kilogram kelvin"

wattPerMetreKelvin : SI.Unit ThermalConductivity
wattPerMetreKelvin = SI.mkUnit "W m⁻¹ K⁻¹" "watt per metre kelvin"

record AMRMeasurementBundle : Set₁ where
  field
    temperatureScale fieldStrengthScale fluxDensityScale : SI.DecimalScale
    entropyScale heatCapacityScale specificHeatScale conductivityScale : SI.DecimalScale
    pressureScale flowScale energyScale powerScale : SI.DecimalScale

    temperature : SI.Measurement SI.Temperature temperatureScale
    magneticFieldStrength : SI.Measurement MagneticFieldStrength fieldStrengthScale
    magneticFluxDensity : SI.Measurement SI.MagneticFluxDensity fluxDensityScale
    entropyChange : SI.Measurement Entropy entropyScale
    heatCapacity : SI.Measurement HeatCapacity heatCapacityScale
    specificHeatCapacity : SI.Measurement SpecificHeatCapacity specificHeatScale
    thermalConductivity : SI.Measurement ThermalConductivity conductivityScale
    pressureDrop : SI.Measurement SI.Pressure pressureScale
    volumetricFlowRate : SI.Measurement SI.VolumetricFlowRate flowScale
    coolingEnergy : SI.Measurement SI.Energy energyScale
    coolingPower : SI.Measurement SI.Power powerScale
    inputPower : SI.Measurement SI.Power powerScale

record MagnetocaloricSIMaterialCrosswalk
  (M : MCE.MagnetocaloricMaterial)
  (B : AMRMeasurementBundle) : Set₁ where
  open MCE.MagnetocaloricMaterial M
  field
    TemperatureIdentification : Set
    MaterialFieldConvention : Set
    EntropyIdentification : Set
    HeatCapacityIdentification : Set
    ConductivityIdentification : Set

    temperatureIdentification : TemperatureIdentification
    materialFieldConvention : MaterialFieldConvention
    entropyIdentification : EntropyIdentification
    heatCapacityIdentification : HeatCapacityIdentification
    conductivityIdentification : ConductivityIdentification

    CalibrationTraceable : Set
    calibrationTraceable : CalibrationTraceable

record MagnetocaloricSIMetrologyBoundary : Set where
  constructor magnetocaloric-si-metrology-boundary
  field
    teslaIsFluxDensityNotFieldStrength : Bool
    fieldStrengthUsesAmperePerMetre : Bool
    typedQuantityDoesNotSupplyConstitutiveLaw : Bool
    typedQuantityDoesNotSupplyCalibration : Bool
    commonPowerDimensionDoesNotProveCOP : Bool

canonicalMagnetocaloricSIMetrologyBoundary : MagnetocaloricSIMetrologyBoundary
canonicalMagnetocaloricSIMetrologyBoundary =
  magnetocaloric-si-metrology-boundary true true true true true
