module DASHI.Physics.Optics.OpticalPhenomenaKernelBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Optics.PhysicalConstantsKernelClosure as Constants

------------------------------------------------------------------------
-- Fail-closed contact surface between the DASHI kernel vocabulary and
-- standard optical laws.  The module records which observable follows
-- once the required physical carrier, constitutive law, boundary data,
-- and approximation regime are supplied.  It does not derive water's
-- dispersion curve, molecular polarizability, or detector colour space.

data OpticalKernelDepth : Set where
  maxwellPropagationDepth : OpticalKernelDepth
  constitutiveResponseDepth : OpticalKernelDepth
  boundaryGeometryDepth : OpticalKernelDepth
  farFieldObservationDepth : OpticalKernelDepth
  perceptualProjectionDepth : OpticalKernelDepth

data ApproximationRegime : Set where
  exactIdentity : ApproximationRegime
  dipoleLimit : ApproximationRegime
  fraunhoferLimit : ApproximationRegime
  geometricalOpticsLimit : ApproximationRegime
  observerModelRequired : ApproximationRegime

data PromotionBoundary : Set where
  symbolicLawOnly : PromotionBoundary
  materialCalibrationRequired : PromotionBoundary
  geometryCalibrationRequired : PromotionBoundary
  empiricalValidationRequired : PromotionBoundary

record KernelLawBridge : Set where
  field
    phenomenon : String
    sourceKernel : OpticalKernelDepth
    targetKernel : OpticalKernelDepth
    physicalLaw : String
    observableMap : String
    regime : ApproximationRegime
    requiredInputs : List String
    constantsUsed : List String
    omittedPhysics : List String
    boundary : PromotionBoundary

open KernelLawBridge public

maxwellPhaseTransport : KernelLawBridge
maxwellPhaseTransport = record
  { phenomenon = "vacuum phase propagation"
  ; sourceKernel = maxwellPropagationDepth
  ; targetKernel = farFieldObservationDepth
  ; physicalLaw = "omega = c k and c^2 = 1 / (epsilon_0 mu_0)"
  ; observableMap = "frequency omega <-> wavelength lambda = 2 pi c / omega"
  ; regime = exactIdentity
  ; requiredInputs = "Lorentzian vacuum constitutive law" ∷ []
  ; constantsUsed = "c" ∷ "epsilon_0" ∷ "mu_0" ∷ []
  ; omittedPhysics = "medium dispersion" ∷ "source bandwidth" ∷ []
  ; boundary = symbolicLawOnly
  }

rayleighDipoleBridge : KernelLawBridge
rayleighDipoleBridge = record
  { phenomenon = "Rayleigh scattering"
  ; sourceKernel = constitutiveResponseDepth
  ; targetKernel = farFieldObservationDepth
  ; physicalLaw =
      "sigma_R = (8 pi / 3) k^4 |alpha_pol|^2 / (4 pi epsilon_0)^2"
  ; observableMap =
      "lambda -> sigma_R(lambda); for slowly varying alpha_pol, sigma_R proportional to lambda^-4"
  ; regime = dipoleLimit
  ; requiredInputs =
      "scatterer size a satisfies a << lambda"
      ∷ "electric polarizability alpha_pol(omega)"
      ∷ "single-scattering or controlled optical depth"
      ∷ []
  ; constantsUsed = "c" ∷ "epsilon_0" ∷ []
  ; omittedPhysics =
      "Mie multipoles"
      ∷ "multiple scattering"
      ∷ "absorption and resonant dispersion"
      ∷ "human cone response"
      ∷ []
  ; boundary = materialCalibrationRequired
  }

rayleighSphereCancellationBridge : KernelLawBridge
rayleighSphereCancellationBridge = record
  { phenomenon = "small dielectric sphere Rayleigh closure"
  ; sourceKernel = constitutiveResponseDepth
  ; targetKernel = farFieldObservationDepth
  ; physicalLaw =
      "alpha_pol = 4 pi epsilon_0 a^3 (epsilon_r - 1)/(epsilon_r + 2)"
  ; observableMap =
      "sigma_R = (8 pi / 3) k^4 a^6 |(epsilon_r - 1)/(epsilon_r + 2)|^2"
  ; regime = dipoleLimit
  ; requiredInputs =
      "homogeneous nonmagnetic sphere"
      ∷ "quasistatic internal field"
      ∷ "a << lambda"
      ∷ []
  ; constantsUsed = "c through k = omega/c" ∷ []
  ; omittedPhysics =
      "finite-size Mie corrections"
      ∷ "magnetic response"
      ∷ "nonspherical shape tensor"
      ∷ []
  ; boundary = materialCalibrationRequired
  }

singleSlitDiffractionBridge : KernelLawBridge
singleSlitDiffractionBridge = record
  { phenomenon = "single-slit Fraunhofer diffraction"
  ; sourceKernel = boundaryGeometryDepth
  ; targetKernel = farFieldObservationDepth
  ; physicalLaw =
      "I(theta)/I_0 = sinc^2(pi a sin(theta) / lambda)"
  ; observableMap =
      "(lambda , aperture width a) -> angular intensity profile"
  ; regime = fraunhoferLimit
  ; requiredInputs =
      "coherent monochromatic incident field"
      ∷ "known aperture transmission"
      ∷ "far-field or Fourier-plane observation"
      ∷ []
  ; constantsUsed = "c only when converting lambda <-> frequency" ∷ []
  ; omittedPhysics =
      "near-field Fresnel terms"
      ∷ "partial coherence"
      ∷ "vector-polarisation aperture corrections"
      ∷ []
  ; boundary = geometryCalibrationRequired
  }

primaryRainbowBridge : KernelLawBridge
primaryRainbowBridge = record
  { phenomenon = "primary water-droplet rainbow"
  ; sourceKernel = constitutiveResponseDepth
  ; targetKernel = farFieldObservationDepth
  ; physicalLaw =
      "D_1(i,lambda) = pi + 2 i - 4 asin(sin(i)/n(lambda)); rainbow at partial D_1 / partial i = 0"
  ; observableMap =
      "lambda -> n(lambda) -> stationary deflection angle -> spectral caustic"
  ; regime = geometricalOpticsLimit
  ; requiredInputs =
      "wavelength-dependent refractive index n(lambda)"
      ∷ "approximately spherical droplets"
      ∷ "one internal reflection"
      ∷ "droplet radius large compared with wavelength"
      ∷ []
  ; constantsUsed =
      "c when frequency is converted to vacuum wavelength"
      ∷ []
  ; omittedPhysics =
      "Airy interference and supernumerary bows"
      ∷ "polarisation-dependent Fresnel amplitudes"
      ∷ "droplet-size distribution"
      ∷ "atmospheric attenuation"
      ∷ "display RGB conversion"
      ∷ []
  ; boundary = materialCalibrationRequired
  }

spectralColourProjectionBridge : KernelLawBridge
spectralColourProjectionBridge = record
  { phenomenon = "displayed rainbow colour"
  ; sourceKernel = farFieldObservationDepth
  ; targetKernel = perceptualProjectionDepth
  ; physicalLaw =
      "spectral radiance -> cone fundamentals / colour matching functions -> display gamut"
  ; observableMap =
      "spectral power distribution -> tristimulus coordinates -> rendered RGB"
  ; regime = observerModelRequired
  ; requiredInputs =
      "spectral radiance"
      ∷ "chosen standard observer"
      ∷ "illuminant and adaptation convention"
      ∷ "display transfer function and gamut"
      ∷ []
  ; constantsUsed = "none beyond spectral-frequency conversion" ∷ []
  ; omittedPhysics =
      "individual observer variation"
      ∷ "surround and adaptation effects"
      ∷ "metameric ambiguity"
      ∷ []
  ; boundary = empiricalValidationRequired
  }

record OpticalPhenomenaKernelClosure : Set where
  field
    constantClosure : Constants.PhysicalConstantsKernelClosure
    bridges : List KernelLawBridge
    maxwellCompatible : Bool
    maxwellCompatibleIsTrue : maxwellCompatible ≡ true
    rayleighExponentConditioned : Bool
    rayleighExponentConditionedIsTrue : rayleighExponentConditioned ≡ true
    renderedRGBIsPhysicalSpectrum : Bool
    renderedRGBIsPhysicalSpectrumIsFalse : renderedRGBIsPhysicalSpectrum ≡ false
    derivesMaterialDispersion : Bool
    derivesMaterialDispersionIsFalse : derivesMaterialDispersion ≡ false
    promotedAsNewPhysics : Bool
    promotedAsNewPhysicsIsFalse : promotedAsNewPhysics ≡ false

open OpticalPhenomenaKernelClosure public

canonicalOpticalPhenomenaKernelClosure : OpticalPhenomenaKernelClosure
canonicalOpticalPhenomenaKernelClosure = record
  { constantClosure = Constants.canonicalPhysicalConstantsKernelClosure
  ; bridges =
      maxwellPhaseTransport
      ∷ rayleighDipoleBridge
      ∷ rayleighSphereCancellationBridge
      ∷ singleSlitDiffractionBridge
      ∷ primaryRainbowBridge
      ∷ spectralColourProjectionBridge
      ∷ []
  ; maxwellCompatible = true
  ; maxwellCompatibleIsTrue = refl
  ; rayleighExponentConditioned = true
  ; rayleighExponentConditionedIsTrue = refl
  ; renderedRGBIsPhysicalSpectrum = false
  ; renderedRGBIsPhysicalSpectrumIsFalse = refl
  ; derivesMaterialDispersion = false
  ; derivesMaterialDispersionIsFalse = refl
  ; promotedAsNewPhysics = false
  ; promotedAsNewPhysicsIsFalse = refl
  }
