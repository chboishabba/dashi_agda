module DASHI.Physics.Textile.TextileIridescentAppearanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Textile.TextileBirefringenceRetardanceExact as Birefringence
import DASHI.Physics.Textile.TextileAngularAppearanceExact as Angular
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Iridescence as observer/illumination-conditioned spectral appearance.
--
-- A colour or radiance change with geometry is an observation.  Assigning a
-- physical cause (birefringence, thin-film interference, diffraction, etc.)
-- requires a separate mechanism receipt.  This prevents inverse inference from
-- appearance alone.
------------------------------------------------------------------------

data IridescenceMechanism : Set where
  birefringentRetardance : IridescenceMechanism
  thinFilmInterference : IridescenceMechanism
  diffractiveMicrostructure : IridescenceMechanism
  mixedOrOtherMechanism : IridescenceMechanism

record IridescentAppearanceWitness
    {OpticalState Illumination OpticalObserver Radiance Wavelength : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (state : OpticalState) : Set₁ where
  constructor iridescent-appearance-witness
  field
    firstObserver : OpticalObserver
    secondObserver : OpticalObserver
    firstWavelength : Wavelength
    secondWavelength : Wavelength

    firstObservation :
      Optical.TextileRadianceObservation model state firstObserver
    secondObservation :
      Optical.TextileRadianceObservation model state secondObserver

    observerOrSpectralCoordinateDiffers :
      (firstObserver ≡ secondObserver) →
      (firstWavelength ≡ secondWavelength) →
      ⊥

    observedAppearanceDiffers :
      Optical.radianceSample firstObservation
      ≡ Optical.radianceSample secondObservation
      → ⊥

open IridescentAppearanceWitness public

record MechanismConditionedIridescence
    {OpticalState Illumination OpticalObserver Radiance Wavelength Scalar : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (state : OpticalState) : Set₁ where
  constructor mechanism-conditioned-iridescence
  field
    observation :
      IridescentAppearanceWitness
        {Wavelength = Wavelength}
        model state

    mechanism : IridescenceMechanism
    mechanismAuthority : String
    mechanismCalibration : String

    birefringenceReceiptWhenClaimed :
      mechanism ≡ birefringentRetardance →
      Σ (Birefringence.TextileBirefringenceCalibration Scalar)
        (λ calibration → String)

open MechanismConditionedIridescence public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data ColourShiftProvesBirefringence : Set where

colourShiftDoesNotProveBirefringence :
  ColourShiftProvesBirefringence → ⊥
colourShiftDoesNotProveBirefringence ()

data IridescenceWitnessDeterminesUniquePhysicalMechanism : Set where

iridescenceWitnessDoesNotDetermineUniquePhysicalMechanism :
  IridescenceWitnessDeterminesUniquePhysicalMechanism → ⊥
iridescenceWitnessDoesNotDetermineUniquePhysicalMechanism ()

data IridescenceIsSameObservableAsSpecularGloss : Set where

iridescenceIsNotSameObservableAsSpecularGloss :
  IridescenceIsSameObservableAsSpecularGloss → ⊥
iridescenceIsNotSameObservableAsSpecularGloss ()
