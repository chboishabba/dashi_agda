module DASHI.Physics.Closure.ApertureWakeModeSelectionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.ContextConditionedTrajectoryWeightExact as Weight
import DASHI.Physics.Foundations.WavelengthSourceScaleSelectionExact as Scale
import DASHI.Physics.Foundations.PathIntegralExperimentalSourceRegistryExact as Sources
import DASHI.Interop.StationaryPhaseMirrorGratingToyReceipt as Toy
import DASHI.Physics.Closure.LightTransportFibreClosure as Light
import DASHI.Physics.Closure.QuantumPathFibreObservationQuotient as Quantum

------------------------------------------------------------------------
-- Cross-domain consumer of the generic wavelength/source-scale owner.
--
-- Aperture/grating optics and finite-source Kelvin wakes share the abstract
-- pattern
--
--   admissible modes -> source-scale coordinate -> context-dependent weight
--                    -> stationary/coherent observable structure
--
-- while retaining different physical laws and source provenance.
------------------------------------------------------------------------

data ModeSelectionDomain : Set where
  apertureDiffractionDomain : ModeSelectionDomain
  finiteSourceKelvinWakeDomain : ModeSelectionDomain

data ModeSelectionRole : Set where
  apertureAngularWeightingRole : ModeSelectionRole
  wakeDominantAmplitudeRole : ModeSelectionRole

roleForDomain : ModeSelectionDomain → ModeSelectionRole
roleForDomain apertureDiffractionDomain = apertureAngularWeightingRole
roleForDomain finiteSourceKelvinWakeDomain = wakeDominantAmplitudeRole

apertureAndWakeModeRolesAreDistinct :
  apertureAngularWeightingRole ≡ wakeDominantAmplitudeRole → ⊥
apertureAndWakeModeRolesAreDistinct ()

------------------------------------------------------------------------
-- Existing optical transport surfaces are consumed directly.
------------------------------------------------------------------------

stationaryPhaseOpticsReceipt :
  Toy.StationaryPhaseMirrorGratingToyReceipt
    Toy.QL.canonicalQuantumPathLightTransportAnalogyDischarge
stationaryPhaseOpticsReceipt =
  Toy.canonicalStationaryPhaseMirrorGratingToyReceipt

quantumPathSurface : Quantum.QuantumPathFibreObservationQuotient
quantumPathSurface =
  Toy.quantumSurface stationaryPhaseOpticsReceipt

lightTransportSurface : Light.LightTransportFibreClosure
lightTransportSurface =
  Toy.lightSurface stationaryPhaseOpticsReceipt

apertureScale : Scale.SourceScaleCoordinate
apertureScale = Scale.canonicalApertureScaleCoordinate

wakeScale : Scale.SourceScaleCoordinate
wakeScale = Scale.canonicalWakeScaleCoordinate

scaleWeightBridge :
  Scale.ScaleConditionedWeightBridge Weight.canonicalContextConditionedTrajectoryWeight
scaleWeightBridge =
  Scale.canonicalScaleConditionedWeightBridge

------------------------------------------------------------------------
-- Source-bounded domain bridge.
------------------------------------------------------------------------

record ApertureWakeModeSelectionBridge : Set₁ where
  field
    scaleBoundary : Scale.WavelengthSourceScaleBoundary
    weightBoundary : Weight.ContextConditionedWeightBoundary

    opticalQuantumSurface : Quantum.QuantumPathFibreObservationQuotient
    opticalLightTransportSurface : Light.LightTransportFibreClosure

    opticsSource : Sources.SourceReference
    finiteWakeSource2013 : Sources.SourceReference
    finiteWakeSource2014 : Sources.SourceReference

    apertureCoordinate : Scale.SourceScaleCoordinate
    wakeCoordinate : Scale.SourceScaleCoordinate

    reducedWakeFroudeCoordinate : Scale.ReducedWakeFroudeCoordinate

    sameGenericRatioShapePromotesSamePhysics : Bool
    sameGenericRatioShapePromotesSamePhysicsIsFalse :
      sameGenericRatioShapePromotesSamePhysics ≡ false

    wavelengthScaleAloneFixesObservedPattern : Bool
    wavelengthScaleAloneFixesObservedPatternIsFalse :
      wavelengthScaleAloneFixesObservedPattern ≡ false

    sourceWeightingEqualsStationarySelection : Bool
    sourceWeightingEqualsStationarySelectionIsFalse :
      sourceWeightingEqualsStationarySelection ≡ false

    bridgeReading : String

open ApertureWakeModeSelectionBridge public

canonicalApertureWakeModeSelectionBridge : ApertureWakeModeSelectionBridge
canonicalApertureWakeModeSelectionBridge =
  record
    { scaleBoundary =
        Scale.canonicalWavelengthSourceScaleBoundary
    ; weightBoundary =
        Weight.canonicalContextConditionedWeightBoundary
    ; opticalQuantumSurface =
        quantumPathSurface
    ; opticalLightTransportSurface =
        lightTransportSurface
    ; opticsSource =
        Sources.bornWolfPrinciplesOfOptics
    ; finiteWakeSource2013 =
        Sources.rabaudMoisy2013
    ; finiteWakeSource2014 =
        Sources.darmonBenzaquenRaphael2014
    ; apertureCoordinate =
        apertureScale
    ; wakeCoordinate =
        wakeScale
    ; reducedWakeFroudeCoordinate =
        Scale.canonicalReducedWakeFroudeCoordinate
    ; sameGenericRatioShapePromotesSamePhysics =
        false
    ; sameGenericRatioShapePromotesSamePhysicsIsFalse =
        refl
    ; wavelengthScaleAloneFixesObservedPattern =
        false
    ; wavelengthScaleAloneFixesObservedPatternIsFalse =
        refl
    ; sourceWeightingEqualsStationarySelection =
        false
    ; sourceWeightingEqualsStationarySelectionIsFalse =
        refl
    ; bridgeReading =
        "Aperture diffraction and finite-source Kelvin wakes reuse one source-scale/weighting architecture, but optical diffraction, wake dispersion, source weighting, and stationary/coherent selection remain separately typed physical roles."
    }
