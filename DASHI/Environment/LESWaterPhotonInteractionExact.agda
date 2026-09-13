module DASHI.Environment.LESWaterPhotonInteractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESFluidPhysicsCouplingExact as Fluid
import DASHI.Environment.LESPhysicalPhotonTransportFibreExact as Photon
import DASHI.Physics.Optics.GeometricalOpticsRefractionLensPrismExact as Geo

------------------------------------------------------------------------
-- SOURCE-BOUND WATER OPTICS
--
-- These records bind measurement authority to specific optical coordinates.
-- They do not manufacture a universal optical model of arbitrary pond, river,
-- seawater, soil water, or biological fluid.
------------------------------------------------------------------------

record WaterOpticsSource : Set where
  constructor water-optics-source
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    boundedRole : String
    excludedPromotion : String

open WaterOpticsSource public

haleQuerry1973 : WaterOpticsSource
haleQuerry1973 = water-optics-source
  "George M. Hale and Marvin R. Querry"
  "Optical Constants of Water in the 200-nm to 200-um Wavelength Region"
  "Applied Optics 12(3), 555-563"
  1973
  "DOI 10.1364/AO.12.000555"
  "Measurement authority for wavelength-dependent refractive index and extinction coefficient of water under the reported experimental conditions."
  "Does not provide one universal natural-water optical state or eliminate temperature, salinity, dissolved matter, particulate scattering, bubbles, interfaces, or calibration."

popeFry1997 : WaterOpticsSource
popeFry1997 = water-optics-source
  "Robin M. Pope and Edward S. Fry"
  "Absorption spectrum (380-700 nm) of pure water. II. Integrating cavity measurements"
  "Applied Optics 36(33), 8710-8723"
  1997
  "DOI 10.1364/AO.36.008710"
  "Measurement authority for visible-spectrum absorption of pure water under the reported integrating-cavity experiment."
  "Does not establish absorption of arbitrary environmental water containing dissolved or suspended constituents."

pegauGrayZaneveld1997 : WaterOpticsSource
pegauGrayZaneveld1997 = water-optics-source
  "W. Scott Pegau, David Gray and J. Ronald V. Zaneveld"
  "Absorption and attenuation of visible and near-infrared light in water: dependence on temperature and salinity"
  "Applied Optics 36(24), 6035-6046"
  1997
  "DOI 10.1364/AO.36.006035"
  "Measurement authority for temperature- and salinity-conditioned absorption/attenuation changes in the reported visible and near-infrared regime."
  "Does not make temperature and salinity the only controls on natural-water optics."

------------------------------------------------------------------------
-- Calibrated optical state of water.
------------------------------------------------------------------------

record WaterOpticalCalibration
    (Scalar Wavelength Temperature Salinity : Set) : Set₁ where
  constructor water-optical-calibration
  field
    refractiveIndex : Wavelength → Temperature → Salinity → Scalar
    extinctionCoefficient : Wavelength → Temperature → Salinity → Scalar
    absorptionCoefficient : Wavelength → Temperature → Salinity → Scalar
    attenuationCoefficient : Wavelength → Temperature → Salinity → Scalar
    scatteringCoefficient : Wavelength → Temperature → Salinity → Scalar

    refractiveIndexAuthority : WaterOpticsSource
    absorptionAuthority : WaterOpticsSource
    temperatureSalinityAuthority : WaterOpticsSource
    scatteringCalibrationReference : String
    constituentCalibrationReference : String
    validityDomainReference : String
    uncertaintyReference : String

open WaterOpticalCalibration public

------------------------------------------------------------------------
-- Same-object fluid / optical state weld.
------------------------------------------------------------------------

record WaterFluidOpticsWeld
    {Scalar Wavelength Temperature Salinity : Set}
    (fluid : Fluid.FluidReductionReceipt)
    (optics : WaterOpticalCalibration Scalar Wavelength Temperature Salinity)
    : Set₁ where
  constructor water-fluid-optics-weld
  field
    WaterState : Set
    fluidState : WaterState → Fluid.FluidState (Fluid.fieldSocket fluid)
    temperature : WaterState → Temperature
    salinity : WaterState → Salinity
    wavelengthSupportReference : String
    sameSpaceTimeReference : String
    densityTemperatureSalinityReference : String
    constituentStateReference : String
    interfaceGeometryReference : String
    validationReference : String

open WaterFluidOpticsWeld public

------------------------------------------------------------------------
-- Photon-event interaction with the literal same water state.
------------------------------------------------------------------------

record WaterPhotonInteraction
    {FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight : Set}
    {Scalar Temperature Salinity : Set}
    (photon : Photon.PhotonTransportFibre
      FineEvent RayBundle Cell Time Wavelength Polarization Medium Weight)
    (fluid : Fluid.FluidReductionReceipt)
    (optics : WaterOpticalCalibration Scalar Wavelength Temperature Salinity)
    (water : WaterFluidOpticsWeld fluid optics)
    : Set₁ where
  constructor water-photon-interaction
  field
    incidentEvent : FineEvent
    outgoingEvent : FineEvent
    localWaterState : WaterState water

    opticalAlgebra : Geo.GeometricalOpticsAlgebra Scalar
    interfaceRefraction : Geo.SnellRefractionReceipt opticalAlgebra

    wavelengthIsRetained :
      Photon.wavelength photon outgoingEvent ≡ Photon.wavelength photon incidentEvent

    absorptionApplicationReference : String
    scatteringApplicationReference : String
    attenuationPathLengthReference : String
    reflectedTransmittedPartitionReference : String
    polarizationUpdateReference : String
    depositedEnergyReference : String
    thermalFeedbackReference : String
    fluidMotionOpticsFeedbackReference : String
    commonSpaceTimeReference : String
    interactionValidationReference : String

open WaterPhotonInteraction public

------------------------------------------------------------------------
-- Optical changes induced by moving/deforming water require an explicit
-- fluid-to-optics observer rather than being inferred from the word "water".
------------------------------------------------------------------------

record DynamicWaterOpticalObserver
    {Scalar Wavelength Temperature Salinity Observation : Set}
    (fluid : Fluid.FluidReductionReceipt)
    (optics : WaterOpticalCalibration Scalar Wavelength Temperature Salinity)
    (water : WaterFluidOpticsWeld fluid optics) : Set₁ where
  constructor dynamic-water-optical-observer
  field
    observeWaterOptics : WaterState water → Observation
    freeSurfaceGeometryReference : String
    refractiveInterfaceReference : String
    suspendedMatterReference : String
    bubbleFoamReference : String
    turbulenceInterfaceReference : String
    observerValidationReference : String

open DynamicWaterOpticalObserver public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data PureWaterConstantsAreUniversalNaturalWaterConstants : Set where
pureWaterConstantsAreNotUniversalNaturalWaterConstants :
  PureWaterConstantsAreUniversalNaturalWaterConstants → ⊥
pureWaterConstantsAreNotUniversalNaturalWaterConstants ()

data RefractiveIndexAloneDeterminesWaterLightTransport : Set where
refractiveIndexAloneDoesNotDetermineWaterLightTransport :
  RefractiveIndexAloneDeterminesWaterLightTransport → ⊥
refractiveIndexAloneDoesNotDetermineWaterLightTransport ()

data FluidStateAloneDeterminesOpticalState : Set where
fluidStateAloneDoesNotDetermineOpticalState :
  FluidStateAloneDeterminesOpticalState → ⊥
fluidStateAloneDoesNotDetermineOpticalState ()

data WaterOpticsReceiptIsNavierStokesSolution : Set where
waterOpticsReceiptIsNotNavierStokesSolution :
  WaterOpticsReceiptIsNavierStokesSolution → ⊥
waterOpticsReceiptIsNotNavierStokesSolution ()

data AbsorbedPhotonEnergyAutomaticallyMeansPhotosynthesis : Set where
absorbedPhotonEnergyDoesNotAutomaticallyMeanPhotosynthesis :
  AbsorbedPhotonEnergyAutomaticallyMeansPhotosynthesis → ⊥
absorbedPhotonEnergyDoesNotAutomaticallyMeanPhotosynthesis ()
