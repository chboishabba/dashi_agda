module DASHI.Physics.Optics.MultiscaleApertureSynthesisKernelBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Compatibility surface for multiscale aperture synthesis imaging.
--
-- The relevant physics is not a violation of Maxwell diffraction.  The
-- instrument changes the measurement operator: separated coded sensors
-- acquire overlapping diffraction data, recover local complex fields,
-- estimate relative phase gauges, and synthesize a larger effective
-- aperture.  Resolution remains constrained by wavelength, collected
-- spatial-frequency support, SNR, calibration, and identifiability.

data SynthesisStage : Set where
  codedDiffractionMeasurement : SynthesisStage
  localComplexFieldRecovery : SynthesisStage
  phaseGaugeSynchronization : SynthesisStage
  syntheticApertureUnion : SynthesisStage
  numericalBackPropagation : SynthesisStage
  objectEstimate : SynthesisStage

data LimitClass : Set where
  singleApertureDiffractionLimit : LimitClass
  syntheticApertureSupportLimit : LimitClass
  noiseInformationLimit : LimitClass
  calibrationIdentifiabilityLimit : LimitClass
  samplingAliasingLimit : LimitClass

record SynthesisStep : Set where
  field
    stage : SynthesisStage
    inputCarrier : String
    operator : String
    outputCarrier : String
    kernelReading : String
    requiredConditions : List String

open SynthesisStep public

measurementStep : SynthesisStep
measurementStep = record
  { stage = codedDiffractionMeasurement
  ; inputCarrier = "object complex field"
  ; operator = "coded free-space diffraction measurement at sensor q"
  ; outputCarrier = "intensity / diffraction data y_q"
  ; kernelReading = "sensor-specific observation kernel"
  ; requiredConditions =
      "known sensor location and code"
      ∷ "controlled wavelength band"
      ∷ "sampling sufficient for measured diffraction support"
      ∷ []
  }

fieldRecoveryStep : SynthesisStep
fieldRecoveryStep = record
  { stage = localComplexFieldRecovery
  ; inputCarrier = "coded intensity measurements y_q"
  ; operator = "phase-retrieval inverse map"
  ; outputCarrier = "local complex wavefield E_q up to gauge"
  ; kernelReading = "hidden phase lift constrained by redundant measurements"
  ; requiredConditions =
      "phase retrieval identifiable under selected coding"
      ∷ "noise model and regularisation declared"
      ∷ []
  }

phaseSynchronizationStep : SynthesisStep
phaseSynchronizationStep = record
  { stage = phaseGaugeSynchronization
  ; inputCarrier = "local wavefields E_q exp(i phi_q)"
  ; operator = "relative phase-offset estimation over overlap graph"
  ; outputCarrier = "gauge-aligned wavefields"
  ; kernelReading = "quotient local U(1) representatives to a coherent global section"
  ; requiredConditions =
      "connected overlap graph"
      ∷ "sufficient common spatial-frequency support"
      ∷ "global phase remains physically irrelevant"
      ∷ []
  }

apertureUnionStep : SynthesisStep
apertureUnionStep = record
  { stage = syntheticApertureUnion
  ; inputCarrier = "gauge-aligned sensor Fourier patches"
  ; operator = "weighted union / coherent fusion"
  ; outputCarrier = "expanded spatial-frequency support"
  ; kernelReading = "join of compatible observation kernels"
  ; requiredConditions =
      "relative phase calibration accepted"
      ∷ "overlap consistency residual bounded"
      ∷ []
  }

backPropagationStep : SynthesisStep
backPropagationStep = record
  { stage = numericalBackPropagation
  ; inputCarrier = "synthetic-aperture complex field"
  ; operator = "angular-spectrum or Fresnel propagator"
  ; outputCarrier = "object-plane field estimate"
  ; kernelReading = "inverse physical transport on the admitted wave manifold"
  ; requiredConditions =
      "propagation model matches geometry and wavelength"
      ∷ "evanescent components are not invented without near-field data"
      ∷ []
  }

record MultiscaleApertureSynthesisClosure : Set where
  field
    steps : List SynthesisStep
    respectsMaxwellPropagation : Bool
    respectsMaxwellPropagationIsTrue : respectsMaxwellPropagation ≡ true
    exceedsSingleSensorResolution : Bool
    exceedsSingleSensorResolutionIsTrue : exceedsSingleSensorResolution ≡ true
    violatesDiffractionPhysics : Bool
    violatesDiffractionPhysicsIsFalse : violatesDiffractionPhysics ≡ false
    recoversUnmeasuredSpatialFrequencies : Bool
    recoversUnmeasuredSpatialFrequenciesIsFalse : recoversUnmeasuredSpatialFrequencies ≡ false
    estimatorMayReduceAlignmentError : Bool
    estimatorMayReduceAlignmentErrorIsTrue : estimatorMayReduceAlignmentError ≡ true
    empiricalPerformancePromoted : Bool
    empiricalPerformancePromotedIsFalse : empiricalPerformancePromoted ≡ false
    activeLimits : List LimitClass
    authorityNote : String

open MultiscaleApertureSynthesisClosure public

canonicalMultiscaleApertureSynthesisClosure :
  MultiscaleApertureSynthesisClosure
canonicalMultiscaleApertureSynthesisClosure = record
  { steps =
      measurementStep
      ∷ fieldRecoveryStep
      ∷ phaseSynchronizationStep
      ∷ apertureUnionStep
      ∷ backPropagationStep
      ∷ []
  ; respectsMaxwellPropagation = true
  ; respectsMaxwellPropagationIsTrue = refl
  ; exceedsSingleSensorResolution = true
  ; exceedsSingleSensorResolutionIsTrue = refl
  ; violatesDiffractionPhysics = false
  ; violatesDiffractionPhysicsIsFalse = refl
  ; recoversUnmeasuredSpatialFrequencies = false
  ; recoversUnmeasuredSpatialFrequenciesIsFalse = refl
  ; estimatorMayReduceAlignmentError = true
  ; estimatorMayReduceAlignmentErrorIsTrue = refl
  ; empiricalPerformancePromoted = false
  ; empiricalPerformancePromotedIsFalse = refl
  ; activeLimits =
      syntheticApertureSupportLimit
      ∷ noiseInformationLimit
      ∷ calibrationIdentifiabilityLimit
      ∷ samplingAliasingLimit
      ∷ []
  ; authorityNote =
      "external MASI publication is an empirical authority input; this module records compatibility and proof obligations only"
  }
