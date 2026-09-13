module DASHI.Physics.Optics.AsphericCausticManipulationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.TrajectoryProjectionCausticExact as Caustic
import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi
import DASHI.Physics.Optics.CausticFreeformSourceAtlasExact as Sources
import DASHI.Physics.Optics.AsphericSagSurfaceNormalExact as Sag
import DASHI.Physics.Optics.CatastropheDiffractionNormalFormExact as Diffraction

------------------------------------------------------------------------
-- ANALYSIS / DESIGN BOUNDARY
--
-- Existing repo caustic owner: projection-critical/focused observation.
-- New layer: optical surface geometry + ray/flux map + target illumination.
-- A shaped/aspheric/freeform surface becomes a caustic-design solution only
-- when the producer supplies the relevant ray/flux and integrability receipts.
------------------------------------------------------------------------

data OpticalSurfaceClass : Set where
  sphericalSurface : OpticalSurfaceClass
  conicSurface : OpticalSurfaceClass
  asphericSurface : OpticalSurfaceClass
  freeformSurface : OpticalSurfaceClass
  deformableSurface : OpticalSurfaceClass

record OpticalSurfaceGeometry (SurfacePoint Normal : Set) : Set₁ where
  constructor optical-surface-geometry
  field
    surfaceClass : OpticalSurfaceClass
    point : SurfacePoint → Set
    normalAt : SurfacePoint → Normal
    geometryCalibration : String

open OpticalSurfaceGeometry public

record CausticRayMap
    (SourceRay SurfacePoint TargetPoint Flux : Set) : Set₁ where
  constructor caustic-ray-map
  field
    sourceToSurface : SourceRay → SurfacePoint
    surfaceToTarget : SourceRay → TargetPoint
    sourceFlux : SourceRay → Flux
    targetFlux : TargetPoint → Flux
    transportLaw : String

open CausticRayMap public

record FreeformCausticDesignReceipt
    {SourceRay SurfacePoint TargetPoint Normal Flux : Set}
    (surface : OpticalSurfaceGeometry SurfacePoint Normal)
    (rayMap : CausticRayMap SourceRay SurfacePoint TargetPoint Flux) : Set₁ where
  constructor freeform-caustic-design-receipt
  field
    sourceAuthority : String
    targetIlluminationSpecification : String
    fluxConservationReceipt : String
    normalFieldIntegrabilityReceipt : String
    visibilityOrOcclusionReceipt : String
    refractionOrReflectionLawReceipt : String
    designSource : Sources.CausticFreeformSourceBoundary

open FreeformCausticDesignReceipt public

record AnalyticCausticReceipt
    {History Observation Scalar : Set}
    (project : History → Observation) : Set₁ where
  constructor analytic-caustic-receipt
  field
    jacobianDeterminant : History → Scalar
    criticalHistory : History
    projectedObservation : Observation
    projectionLaw : projectedObservation ≡ project criticalHistory
    jacobianDegeneracyReceipt : String
    catastropheClassificationReceipt : String

open AnalyticCausticReceipt public

record DesignedCausticManipulation
    {SourceRay SurfacePoint TargetPoint Normal Flux Observation : Set}
    (surface : OpticalSurfaceGeometry SurfacePoint Normal)
    (rayMap : CausticRayMap SourceRay SurfacePoint TargetPoint Flux) : Set₁ where
  constructor designed-caustic-manipulation
  field
    design : FreeformCausticDesignReceipt surface rayMap
    targetObservation : Observation
    predictedTargetPattern : Observation
    predictionMatchesTarget : predictedTargetPattern ≡ targetObservation
    validationOrResidualEvidence : String

open DesignedCausticManipulation public

------------------------------------------------------------------------
-- Same-object welds to explicit asphere geometry and local diffraction.
------------------------------------------------------------------------

record AsphericDesignGeometryWeld
    {Scalar SurfacePoint Normal : Set}
    {algebra : Sag.AsphericSagAlgebra Scalar}
    (sag : Sag.RotationalAsphereSagReceipt algebra)
    (normal : Sag.AsphereNormalReceipt sag)
    (surface : OpticalSurfaceGeometry SurfacePoint Normal) : Set₁ where
  constructor aspheric-design-geometry-weld
  field
    surfacePointForSag : SurfacePoint
    surfaceIsAspheric : surfaceClass surface ≡ asphericSurface
    normalIsSameObject : normalAt surface surfacePointForSag ≡ Sag.surfaceNormal normal
    sagGeometryRealisation : String

open AsphericDesignGeometryWeld public

record GeometricToWaveCausticWeld
    {History Observation Scalar : Set}
    {project : History → Observation}
    (analytic : AnalyticCausticReceipt {Scalar = Scalar} project) : Set₁ where
  constructor geometric-to-wave-caustic-weld
  field
    geometricClass : Diffraction.GeometricCausticClassification
    sameCriticalityReading : String
    waveReceipt : Diffraction.CatastropheDiffractionReceipt geometricClass

open GeometricToWaveCausticWeld public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data AsphericSurfaceAutomaticallyCreatesCaustic : Set where
asphericSurfaceDoesNotAutomaticallyCreateCaustic :
  AsphericSurfaceAutomaticallyCreatesCaustic → ⊥
asphericSurfaceDoesNotAutomaticallyCreateCaustic ()

data BrightPatternProvesDesignedCaustic : Set where
brightPatternDoesNotProveDesignedCaustic : BrightPatternProvesDesignedCaustic → ⊥
brightPatternDoesNotProveDesignedCaustic ()

data FiniteProjectionCausticIsContinuumJacobianTheorem : Set where
finiteProjectionCausticIsNotContinuumJacobianTheorem :
  FiniteProjectionCausticIsContinuumJacobianTheorem → ⊥
finiteProjectionCausticIsNotContinuumJacobianTheorem ()

data FreeformDesignReceiptIsFullWaveDiffractionSolution : Set where
freeformDesignReceiptIsNotFullWaveDiffractionSolution :
  FreeformDesignReceiptIsFullWaveDiffractionSolution → ⊥
freeformDesignReceiptIsNotFullWaveDiffractionSolution ()
