module DASHI.Physics.Textile.TextileCausticManipulationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.AsphericCausticManipulationExact as CausticDesign
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Caustic manipulation around or within a textile observation.
-- External optical elements and intrinsic textile microgeometry are separate
-- causal coordinates even when both can produce focused/structured light.
------------------------------------------------------------------------

data TextileCausticRole : Set where
  illuminationTrainCaustic : TextileCausticRole
  observationTrainCaustic : TextileCausticRole
  intrinsicTextileMicrogeometryCaustic : TextileCausticRole

record TextileCausticContext
    {OpticalState Illumination OpticalObserver Radiance : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology) : Set₁ where
  constructor textile-caustic-context
  field
    role : TextileCausticRole
    retainedModel :
      Optical.TextileOpticalModel
        OpticalState Illumination OpticalObserver Radiance topology
    retainedModelIsSameObject : retainedModel ≡ model
    opticalPathDescription : String

open TextileCausticContext public

record ExternalCausticManipulationReceipt
    {OpticalState Illumination OpticalObserver Radiance : Set}
    {SourceRay SurfacePoint TargetPoint Normal Flux Observation : Set}
    {topology : Stitch.StitchState}
    {model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology}
    (context : TextileCausticContext model)
    (surface : CausticDesign.OpticalSurfaceGeometry SurfacePoint Normal)
    (rayMap : CausticDesign.CausticRayMap SourceRay SurfacePoint TargetPoint Flux) : Set₁ where
  constructor external-caustic-manipulation-receipt
  field
    roleIsExternal :
      (role context ≡ illuminationTrainCaustic)
      ⊎ (role context ≡ observationTrainCaustic)
    manipulation :
      CausticDesign.DesignedCausticManipulation
        {Observation = Observation}
        surface rayMap

open ExternalCausticManipulationReceipt public

record IntrinsicTextileCausticRealisation
    {OpticalState Illumination OpticalObserver Radiance : Set}
    {SourceRay SurfacePoint TargetPoint Normal Flux Observation : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (surface : CausticDesign.OpticalSurfaceGeometry SurfacePoint Normal)
    (rayMap : CausticDesign.CausticRayMap SourceRay SurfacePoint TargetPoint Flux) : Set₁ where
  constructor intrinsic-textile-caustic-realisation
  field
    microgeometrySameSpecimenEvidence : String
    surfaceRealisesTextileMicrogeometry : String
    manipulation :
      CausticDesign.DesignedCausticManipulation
        {Observation = Observation}
        surface rayMap
    retainedRadianceState : OpticalState
    retainedObserver : OpticalObserver
    radianceObservation :
      Optical.TextileRadianceObservation model retainedRadianceState retainedObserver

open IntrinsicTextileCausticRealisation public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data ExternalCausticIsIntrinsicTextileLustre : Set where
externalCausticIsNotIntrinsicTextileLustre :
  ExternalCausticIsIntrinsicTextileLustre → ⊥
externalCausticIsNotIntrinsicTextileLustre ()

data TextileLustreProvesIntrinsicCaustic : Set where
textileLustreDoesNotProveIntrinsicCaustic : TextileLustreProvesIntrinsicCaustic → ⊥
textileLustreDoesNotProveIntrinsicCaustic ()

data SameTargetPatternImpliesSameOpticalSurface : Set where
sameTargetPatternDoesNotImplySameOpticalSurface :
  SameTargetPatternImpliesSameOpticalSurface → ⊥
sameTargetPatternDoesNotImplySameOpticalSurface ()
