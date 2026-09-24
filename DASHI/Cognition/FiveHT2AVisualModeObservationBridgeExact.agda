module DASHI.Cognition.FiveHT2AVisualModeObservationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.FiveHT2AVisualCortexBioelectricBridgeExact as V1
import DASHI.Cognition.ModeGeometrySurface as Mode
import DASHI.Cognition.CorticalLogPolarProjectionGeometry as Geometry
import DASHI.Cognition.KlueverFormConstantProjection as Kluver
import DASHI.Cognition.LogPolarKluverDerivationExact as LogPolar

------------------------------------------------------------------------
-- VISUAL-CIRCUIT OBSERVATION -> MODE-GEOMETRY TARGET
--
-- This does NOT assert that the Barzan/White circuit observations are already
-- Kluever forms.  It creates a testable intermediate:
--
--   source-bound V1 cell/circuit observation
--       -> circuit field / temporal mode candidate
--       -> spatial-mode observation target
--       -> existing log-polar projection / Kluever class comparison.
--
-- Temporal oscillation, response gain and orientation preference remain
-- distinct observables.
------------------------------------------------------------------------

data VisualCircuitModeCoordinate : Set where
  responseGainCoordinate : VisualCircuitModeCoordinate
  orientationTuningCoordinate : VisualCircuitModeCoordinate
  temporalOscillationCoordinate : VisualCircuitModeCoordinate
  spatialPhaseCoordinate : VisualCircuitModeCoordinate
  radialPhaseCoordinate : VisualCircuitModeCoordinate
  angularPhaseCoordinate : VisualCircuitModeCoordinate

data ModeObservationStatus : Set where
  directlyMeasuredCoordinate : ModeObservationStatus
  derivedComparisonTarget : ModeObservationStatus
  notYetMeasured : ModeObservationStatus

record VisualCircuitModeObservation : Set where
  constructor visualCircuitModeObservation
  field
    sourceObservation : V1.VisualCortexSourceObservation
    coordinate : VisualCircuitModeCoordinate
    status : ModeObservationStatus
    reading : String

    spatialKluverClassMeasured : Bool
    spatialKluverClassMeasuredIsFalse :
      spatialKluverClassMeasured ≡ false

open VisualCircuitModeObservation public

barzanVisualGainModeObservation : VisualCircuitModeObservation
barzanVisualGainModeObservation =
  visualCircuitModeObservation
    V1.barzanPVVisualGain
    responseGainCoordinate
    directlyMeasuredCoordinate
    "The source pays a visual-response gain coordinate; gain modulation is not itself a spatial form-constant class."
    false refl

barzanOrientationModeObservation : VisualCircuitModeObservation
barzanOrientationModeObservation =
  visualCircuitModeObservation
    V1.barzanOrientationPreference
    orientationTuningCoordinate
    directlyMeasuredCoordinate
    "Preferred orientation was not shifted at the reported resolution; this separates response gain from orientation tuning."
    false refl

whiteTemporalModeObservation : VisualCircuitModeObservation
whiteTemporalModeObservation =
  visualCircuitModeObservation
    V1.whiteVisualOscillation
    temporalOscillationCoordinate
    directlyMeasuredCoordinate
    "Approximately 5-Hz activity is admitted as a temporal-mode coordinate only; temporal frequency does not determine a spatial Kluever form."
    false refl

canonicalVisualCircuitModeObservations :
  List VisualCircuitModeObservation
canonicalVisualCircuitModeObservations =
  barzanVisualGainModeObservation
  ∷ barzanOrientationModeObservation
  ∷ whiteTemporalModeObservation
  ∷ []

------------------------------------------------------------------------
-- Generic ModeGeometrySurface instance.
--
-- The carrier is source observation identity; the mode spectrum separates
-- gain, orientation, temporal oscillation and the still-unmeasured spatial
-- phase coordinates.  All theorem fields are weak witness Sets, in keeping
-- with the existing generic surface.
------------------------------------------------------------------------

data VisualCircuitCarrier : Set where
  barzanV1Carrier : VisualCircuitCarrier
  whiteV1Carrier : VisualCircuitCarrier

data VisualCircuitSymmetry : Set where
  orientationPreservingSymmetry : VisualCircuitSymmetry
  retinotopicRotationCandidate : VisualCircuitSymmetry
  retinotopicScaleCandidate : VisualCircuitSymmetry

data VisualCircuitModeSpectrum : Set where
  gainMode : VisualCircuitModeSpectrum
  orientationMode : VisualCircuitModeSpectrum
  temporalFiveHzMode : VisualCircuitModeSpectrum
  radialSpatialModeCandidate : VisualCircuitModeSpectrum
  angularSpatialModeCandidate : VisualCircuitModeSpectrum
  mixedLogPolarModeCandidate : VisualCircuitModeSpectrum

VisualCircuitSelectionLaw : VisualCircuitModeSpectrum → Set
VisualCircuitSelectionLaw gainMode = ⊤
VisualCircuitSelectionLaw orientationMode = ⊤
VisualCircuitSelectionLaw temporalFiveHzMode = ⊤
VisualCircuitSelectionLaw radialSpatialModeCandidate = ⊤
VisualCircuitSelectionLaw angularSpatialModeCandidate = ⊤
VisualCircuitSelectionLaw mixedLogPolarModeCandidate = ⊤

data VisualCircuitProjectionGeometry : Set where
  nativeV1Coordinate : VisualCircuitProjectionGeometry
  logPolarProjectionTarget : VisualCircuitProjectionGeometry

data VisualCircuitObservedGeometry : Set where
  gainObservation : VisualCircuitObservedGeometry
  orientationObservation : VisualCircuitObservedGeometry
  temporalOscillationObservation : VisualCircuitObservedGeometry
  spatialFormObservationTarget : VisualCircuitObservedGeometry

canonicalVisualCircuitModeGeometrySurface : Mode.ModeGeometrySurface
canonicalVisualCircuitModeGeometrySurface =
  Mode.modeGeometrySurface
    VisualCircuitCarrier
    VisualCircuitSymmetry
    VisualCircuitModeSpectrum
    VisualCircuitSelectionLaw
    VisualCircuitProjectionGeometry
    VisualCircuitObservedGeometry
    ⊤
    ⊤
    ⊤
    ⊤

canonicalVisualCircuitContactBoundary : Mode.ObservableContactGeometryBoundary
canonicalVisualCircuitContactBoundary =
  Mode.observableContactGeometryBoundary
    canonicalVisualCircuitModeGeometrySurface
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤
    ⊤

------------------------------------------------------------------------
-- Spatial projection target.
------------------------------------------------------------------------

record VisualCircuitToKluverTarget : Set where
  constructor visualCircuitToKluverTarget
  field
    modeSurface : Mode.ModeGeometrySurface
    logPolarBoundary : LogPolar.LogPolarKluverAuthorityBoundary

    spatialFieldProtocolPresent : Bool
    spatialFieldProtocolPresentIsFalse :
      spatialFieldProtocolPresent ≡ false

    retinotopicRegistrationPresent : Bool
    retinotopicRegistrationPresentIsFalse :
      retinotopicRegistrationPresent ≡ false

    phaseModeFitPresent : Bool
    phaseModeFitPresentIsFalse :
      phaseModeFitPresent ≡ false

    kluverClassificationPresent : Bool
    kluverClassificationPresentIsFalse :
      kluverClassificationPresent ≡ false

    temporalFrequencyDeterminesSpatialForm : Bool
    temporalFrequencyDeterminesSpatialFormIsFalse :
      temporalFrequencyDeterminesSpatialForm ≡ false

    responseGainDeterminesSpatialForm : Bool
    responseGainDeterminesSpatialFormIsFalse :
      responseGainDeterminesSpatialForm ≡ false

open VisualCircuitToKluverTarget public

canonicalVisualCircuitToKluverTarget : VisualCircuitToKluverTarget
canonicalVisualCircuitToKluverTarget =
  visualCircuitToKluverTarget
    canonicalVisualCircuitModeGeometrySurface
    LogPolar.canonicalLogPolarKluverAuthorityBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Existing spatial feature vocabulary is consumed as the target codomain.
------------------------------------------------------------------------

targetVisualFeatures : List Geometry.VisualModeFeature
targetVisualFeatures =
  Geometry.translationalPeriodicity
  ∷ Geometry.angularPeriodicity
  ∷ Geometry.radialPeriodicity
  ∷ Geometry.angularPhaseDrift
  ∷ Geometry.radialPhaseDrift
  ∷ Geometry.orientationPinwheelBias
  ∷ Geometry.logRadiusTranslation
  ∷ []

targetKluverForms : List Kluver.KlueverForm
targetKluverForms =
  Kluver.latticeGrating
  ∷ Kluver.tunnelFunnel
  ∷ Kluver.spiral
  ∷ Kluver.radialCobweb
  ∷ []

------------------------------------------------------------------------
-- Anti-collapse.
------------------------------------------------------------------------

data TemporalModeDeterminesSpatialMode : Set where
data GainCoordinateDeterminesFormConstant : Set where
data OrientationUnchangedProvesNoHallucination : Set where

temporalDoesNotDetermineSpatial :
  TemporalModeDeterminesSpatialMode → ⊥
temporalDoesNotDetermineSpatial ()

gainDoesNotDetermineForm :
  GainCoordinateDeterminesFormConstant → ⊥
gainDoesNotDetermineForm ()

orientationUnchangedDoesNotProveNoHallucination :
  OrientationUnchangedProvesNoHallucination → ⊥
orientationUnchangedDoesNotProveNoHallucination ()

------------------------------------------------------------------------
-- Highest-alpha empirical join.
------------------------------------------------------------------------

record VisualModeEmpiricalFrontier : Set where
  constructor visualModeEmpiricalFrontier
  field
    spatialMeasurement : String
    retinotopicMeasurement : String
    perturbationAlignment : String
    modelFit : String
    comparison : String

canonicalVisualModeEmpiricalFrontier : VisualModeEmpiricalFrontier
canonicalVisualModeEmpiricalFrontier =
  visualModeEmpiricalFrontier
    "measure a spatially resolved V1 activity field under 5-HT2A perturbation, not only scalar firing/gain or temporal frequency"
    "bind each spatial sample to retinotopic eccentricity/azimuth coordinates"
    "preserve cell type, ligand/receptor manipulation, dose/time and source protocol through the visual-field readout"
    "fit frozen candidate radial/angular/log-polar phase modes with predeclared residual metric"
    "compare projected mode family to reported form-constant class without using the report to fit the mode parameters"
