module DASHI.Physics.Textile.TextileOpticalTransportBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.ObserverConditionedTransportBridge as Transport
import DASHI.Physics.Optics.OpticalPhenomenaKernelBridge as Optics
import DASHI.Physics.Textile.TextileEmpiricalCalibrationExact as Calibration
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Textile appearance as an exact consumer-specific realization of the
-- repository's existing observer-conditioned light-transport architecture.
--
-- Fabric appearance is not attached directly to a material label.  The same
-- specimen and stitch topology retain separate fiber/surface optical
-- calibration, illumination, transport state, and observer coordinates.
------------------------------------------------------------------------

record TextileOpticalModel
    (OpticalState Illumination OpticalObserver Radiance : Set)
    (topology : Stitch.StitchState) : Set₁ where
  constructor textile-optical-model
  field
    specimen : Calibration.SpecimenIdentity
    fiberOpticalCalibration : String
    surfaceMicrogeometryCalibration : String

    initialOpticalState : OpticalState
    transportLight : Illumination → OpticalState → OpticalState
    observeRadiance : OpticalObserver → OpticalState → Radiance

    retainedTopology : Stitch.StitchState
    retainedTopologyIsSameObject : retainedTopology ≡ topology

open TextileOpticalModel public

textileTransportSystem :
  {OpticalState Illumination OpticalObserver Radiance : Set}
  {topology : Stitch.StitchState} →
  TextileOpticalModel
    OpticalState Illumination OpticalObserver Radiance topology →
  Transport.TransportSystem
textileTransportSystem model = record
  { Transport.State = _
  ; Transport.Source = _
  ; Transport.Observer = _
  ; Transport.Sample = _
  ; Transport.advance = transportLight model
  ; Transport.observe = observeRadiance model
  }

record TextileRadianceObservation
    {OpticalState Illumination OpticalObserver Radiance : Set}
    {topology : Stitch.StitchState}
    (model : TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (state : OpticalState)
    (observer : OpticalObserver) : Set where
  constructor textile-radiance-observation
  field
    radianceSample : Radiance
    sampleIsObserverProjection :
      radianceSample ≡ observeRadiance model observer state

open TextileRadianceObservation public

canonicalTextileRadianceObservation :
  {OpticalState Illumination OpticalObserver Radiance : Set}
  {topology : Stitch.StitchState} →
  (model : TextileOpticalModel
    OpticalState Illumination OpticalObserver Radiance topology) →
  (state : OpticalState) →
  (observer : OpticalObserver) →
  TextileRadianceObservation model state observer
canonicalTextileRadianceObservation model state observer =
  textile-radiance-observation
    (observeRadiance model observer state)
    refl

------------------------------------------------------------------------
-- Metadata-level weld into the existing optical kernel-depth vocabulary.
-- This does not invent a universal cloth BRDF.  It records which physical
-- coordinates must be supplied before a textile radiance observable exists.
------------------------------------------------------------------------

textileAppearanceKernelBridge : Optics.KernelLawBridge
textileAppearanceKernelBridge = record
  { Optics.phenomenon = "textile light transport and appearance"
  ; Optics.sourceKernel = Optics.constitutiveResponseDepth
  ; Optics.targetKernel = Optics.farFieldObservationDepth
  ; Optics.physicalLaw =
      "fiber optical response + yarn/surface geometry + illumination transport -> observer spectral radiance"
  ; Optics.observableMap =
      "(same specimen, topology, optical calibration, illumination, observer) -> radiance sample"
  ; Optics.regime = Optics.observerModelRequired
  ; Optics.requiredInputs =
      "fiber optical calibration"
      ∷ "surface/yarn microgeometry calibration"
      ∷ "textile topology"
      ∷ "illumination geometry and spectrum"
      ∷ "observer geometry / detector response"
      ∷ []
  ; Optics.constantsUsed = []
  ; Optics.omittedPhysics =
      "unresolved sub-fiber scattering"
      ∷ "fluorescence unless separately calibrated"
      ∷ "polarisation unless separately retained"
      ∷ "multiple scattering unless transport model supplies it"
      ∷ []
  ; Optics.boundary = Optics.empiricalValidationRequired
  }

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data SameTextileTopologyDeterminesRadiance : Set where

sameTextileTopologyDoesNotDetermineRadiance :
  SameTextileTopologyDeterminesRadiance → ⊥
sameTextileTopologyDoesNotDetermineRadiance ()

data MaterialLabelDeterminesLustre : Set where

materialLabelDoesNotDetermineLustre :
  MaterialLabelDeterminesLustre → ⊥
materialLabelDoesNotDetermineLustre ()

data OneObserverRadianceSampleDeterminesFullLightField : Set where

oneObserverRadianceSampleDoesNotDetermineFullLightField :
  OneObserverRadianceSampleDeterminesFullLightField → ⊥
oneObserverRadianceSampleDoesNotDetermineFullLightField ()
