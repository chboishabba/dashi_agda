module DASHI.Physics.Textile.TextileAngularAppearanceExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Angular appearance / anisotropy witness.
--
-- Textile appearance can change with observation direction even for the same
-- physical specimen and optical transport state.  This module makes that
-- observer dependence proof-relevant without claiming a complete BRDF model.
------------------------------------------------------------------------

record AngularAppearancePair
    {OpticalState Illumination OpticalObserver Radiance : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (state : OpticalState) : Set₁ where
  constructor angular-appearance-pair
  field
    firstObserver : OpticalObserver
    secondObserver : OpticalObserver

    firstObservation :
      Optical.TextileRadianceObservation model state firstObserver
    secondObservation :
      Optical.TextileRadianceObservation model state secondObserver

open AngularAppearancePair public

record AnisotropicAppearanceWitness
    {OpticalState Illumination OpticalObserver Radiance : Set}
    {topology : Stitch.StitchState}
    {model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology}
    {state : OpticalState}
    (pair : AngularAppearancePair model state) : Set₁ where
  constructor anisotropic-appearance-witness
  field
    observersDiffer : firstObserver pair ≡ secondObserver pair → ⊥
    radianceSamplesDiffer :
      Optical.radianceSample (firstObservation pair)
      ≡ Optical.radianceSample (secondObservation pair)
      → ⊥

open AnisotropicAppearanceWitness public

------------------------------------------------------------------------
-- Observer equivalence remains query-relative.  Equal appearance at one pair
-- of directions does not erase the unresolved full angular response field.
------------------------------------------------------------------------

data TwoAngularSamplesDetermineFullTextileBRDF : Set where

twoAngularSamplesDoNotDetermineFullTextileBRDF :
  TwoAngularSamplesDetermineFullTextileBRDF → ⊥
twoAngularSamplesDoNotDetermineFullTextileBRDF ()

data AnisotropicAppearanceDeterminesFiberMicrogeometry : Set where

anisotropicAppearanceDoesNotDetermineFiberMicrogeometry :
  AnisotropicAppearanceDeterminesFiberMicrogeometry → ⊥
anisotropicAppearanceDoesNotDetermineFiberMicrogeometry ()
