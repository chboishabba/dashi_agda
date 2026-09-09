module DASHI.Physics.Optics.OpticalSurfaceManufacturingToleranceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.AsphericCausticManipulationExact as Caustic
import DASHI.Physics.Optics.InverseCausticNumericalProducerExact as Numerical

------------------------------------------------------------------------
-- DESIGN / FABRICATION / METROLOGY BOUNDARY
--
-- A mathematically valid inverse-design surface is not yet a fabricated optic.
-- This owner retains the tolerance and verification packet required by a
-- concrete manufacturing process.  No single ISO/ASTM tolerance is hard-coded:
-- the applicable drawing/metrology authority is an explicit source coordinate.
------------------------------------------------------------------------

data ManufacturingProcess : Set where
  precisionGrindingPolishing : ManufacturingProcess
  diamondTurning : ManufacturingProcess
  molding : ManufacturingProcess
  lithographicOrAdditive : ManufacturingProcess
  customManufacturingProcess : ManufacturingProcess

record SurfaceToleranceSpecification (Scalar : Set) : Set₁ where
  constructor surface-tolerance-specification
  field
    sagErrorLimit : Scalar
    slopeErrorLimit : Scalar
    surfaceRoughnessLimit : Scalar
    decenterLimit : Scalar
    tiltLimit : Scalar
    clearApertureRequirement : String
    edgeOrThicknessRequirement : String
    drawingOrMetrologyAuthority : String

open SurfaceToleranceSpecification public

record FabricatedOpticalSurface
    {SurfacePoint Normal Scalar : Set}
    (designSurface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal) : Set₁ where
  constructor fabricated-optical-surface
  field
    process : ManufacturingProcess
    partIdentifier : String
    materialBatch : String
    fabricationRecord : String
    measuredGeometry : Caustic.OpticalSurfaceGeometry SurfacePoint Normal

    measuredSagError : Scalar
    measuredSlopeError : Scalar
    measuredSurfaceRoughness : Scalar
    measuredDecenter : Scalar
    measuredTilt : Scalar

open FabricatedOpticalSurface public

record FabricationConformanceReceipt
    {SurfacePoint Normal Scalar : Set}
    {designSurface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal}
    (algebra : Numerical.ResidualAlgebra Scalar)
    (tolerance : SurfaceToleranceSpecification Scalar)
    (fabricated : FabricatedOpticalSurface {Scalar = Scalar} designSurface) : Set₁ where
  constructor fabrication-conformance-receipt
  field
    sagWithinTolerance :
      Numerical._≤_ algebra
        (measuredSagError fabricated)
        (sagErrorLimit tolerance)
    slopeWithinTolerance :
      Numerical._≤_ algebra
        (measuredSlopeError fabricated)
        (slopeErrorLimit tolerance)
    roughnessWithinTolerance :
      Numerical._≤_ algebra
        (measuredSurfaceRoughness fabricated)
        (surfaceRoughnessLimit tolerance)
    decenterWithinTolerance :
      Numerical._≤_ algebra
        (measuredDecenter fabricated)
        (decenterLimit tolerance)
    tiltWithinTolerance :
      Numerical._≤_ algebra
        (measuredTilt fabricated)
        (tiltLimit tolerance)

    metrologyMethod : String
    metrologyDatasetDigest : String
    clearApertureConformance : String
    drawingConformance : String

open FabricationConformanceReceipt public

------------------------------------------------------------------------
-- Optical validation remains downstream of dimensional conformance.
------------------------------------------------------------------------

record FabricatedCausticValidation
    {SurfacePoint Normal Scalar PredictedPattern MeasuredPattern : Set}
    {designSurface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal}
    {algebra : Numerical.ResidualAlgebra Scalar}
    {tolerance : SurfaceToleranceSpecification Scalar}
    {fabricated : FabricatedOpticalSurface {Scalar = Scalar} designSurface}
    (conformance : FabricationConformanceReceipt algebra tolerance fabricated) : Set₁ where
  constructor fabricated-caustic-validation
  field
    predictedPattern : PredictedPattern
    measuredPattern : MeasuredPattern
    comparePattern : PredictedPattern → MeasuredPattern → Scalar
    opticalResidual : Scalar
    comparisonLaw : opticalResidual ≡ comparePattern predictedPattern measuredPattern
    allowedOpticalResidual : Scalar
    opticalResidualAdmissible :
      Numerical._≤_ algebra opticalResidual allowedOpticalResidual

    illuminationCalibration : String
    detectorCalibration : String
    wavelengthAndPolarisationConvention : String
    validationDatasetDigest : String

open FabricatedCausticValidation public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data CADSurfaceEqualsFabricatedSurface : Set where
cadSurfaceDoesNotEqualFabricatedSurfaceByDefinition : CADSurfaceEqualsFabricatedSurface → ⊥
cadSurfaceDoesNotEqualFabricatedSurfaceByDefinition ()

data MetrologyConformanceProvesOpticalPerformance : Set where
metrologyConformanceDoesNotProveOpticalPerformance :
  MetrologyConformanceProvesOpticalPerformance → ⊥
metrologyConformanceDoesNotProveOpticalPerformance ()

data OpticalAgreementProvesUniqueManufacturingProcess : Set where
opticalAgreementDoesNotProveUniqueManufacturingProcess :
  OpticalAgreementProvesUniqueManufacturingProcess → ⊥
opticalAgreementDoesNotProveUniqueManufacturingProcess ()
