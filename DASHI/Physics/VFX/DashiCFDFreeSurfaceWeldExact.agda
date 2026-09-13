module DASHI.Physics.VFX.DashiCFDFreeSurfaceWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.VFX.CoupledPhysicalShotExact as VFX

------------------------------------------------------------------------
-- dashiCFD -> SAME-OBJECT VFX FREE-SURFACE WELD
--
-- The first producer is deliberately reduced-order: conservative 2D
-- Saint-Venant/shallow-water equations with Rusanov fluxes and a fixed solid
-- hull mask.  It produces dimensioned free-surface/velocity/load artifacts,
-- but it is not promoted to 3D VOF/RANS/LES or a calibrated naval prediction.
------------------------------------------------------------------------

record DashiCFDRevision : Set where
  constructor dashi-cfd-revision
  field
    repository : String
    gitRevision : String
    producerPath : String
    runnerPath : String
    numericalModel : String

open DashiCFDRevision public

record FreeSurfaceNumericalReceipt (revision : DashiCFDRevision) : Set where
  constructor free-surface-numerical-receipt
  field
    runArtifactDigest : String
    stateArtifact : String
    receiptArtifact : String

    surfaceHeightDimension : SI.Dimension
    surfaceHeightDimensionIsLength : surfaceHeightDimension ≡ SI.Length
    velocityDimension : SI.Dimension
    velocityDimensionIsVelocity : velocityDimension ≡ SI.Velocity
    pressureDimension : SI.Dimension
    pressureDimensionIsPressure : pressureDimension ≡ SI.Pressure
    resultantLoadDimension : SI.Dimension
    resultantLoadDimensionIsForce : resultantLoadDimension ≡ SI.Force

    gridResolution : String
    physicalDomain : String
    timeHorizon : String
    cflPolicy : String
    boundaryConditionPolicy : String
    hullMaskRevision : String
    waterDensityReference : String
    gravityReference : String

    finiteState : Bool
    finiteStateIsTrue : finiteState ≡ true
    positiveWetDepth : Bool
    positiveWetDepthIsTrue : positiveWetDepth ≡ true
    solidWallDry : Bool
    solidWallDryIsTrue : solidWallDry ≡ true

    domainMassChangeDiagnostic : String
    maxSurfaceDisplacementDiagnostic : String
    hullForceXDiagnostic : String
    hullForceYDiagnostic : String
    calibrationStatus : String
    fidelityStatus : String

open FreeSurfaceNumericalReceipt public

record DashiCFDShotIdentityWeld
    {id : VFX.ShotIdentity}
    (shot : VFX.CoupledPhysicalShot id)
    (revision : DashiCFDRevision)
    (receipt : FreeSurfaceNumericalReceipt revision) : Set₁ where
  constructor dashi-cfd-shot-identity-weld
  field
    shotGeometryEqualsSolverGeometry : String
    shotTimelineEqualsSolverTimeline : String
    shotWaterStateEqualsSolverWaterState : String
    shotHullEqualsSolverHullMask : String
    solverHeightFieldPaysShotFreeSurfaceArtifact : String
    solverVelocityFieldPaysShotWakeArtifact : String
    solverPressureLoadPaysSameVesselState : String
    receiptDigestBindsAllNumericalArtifacts : String

open DashiCFDShotIdentityWeld public

------------------------------------------------------------------------
-- Escalation surface: the reduced producer can pay the old wake/free-surface
-- proxy coordinate, while higher-fidelity effects remain explicit debt.
------------------------------------------------------------------------

record FreeSurfaceFidelityEscalation
    {id : VFX.ShotIdentity}
    {shot : VFX.CoupledPhysicalShot id}
    {revision : DashiCFDRevision}
    {receipt : FreeSurfaceNumericalReceipt revision}
    (weld : DashiCFDShotIdentityWeld shot revision receipt) : Set where
  constructor free-surface-fidelity-escalation
  field
    resolvedByReducedProducer : String
    unresolvedVerticalAcceleration : String
    unresolvedBreakingSprayAirEntrainment : String
    unresolvedThreeDimensionalHullFlow : String
    unresolvedViscousBoundaryLayer : String
    unresolvedTurbulenceClosure : String
    unresolvedMovingDeformingHull : String
    authoritativeEscalationTarget : String

open FreeSurfaceFidelityEscalation public

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data ShallowWaterReceiptIsFullThreeDimensionalFreeSurfaceNS : Set where
shallowWaterReceiptIsNotFullThreeDimensionalFreeSurfaceNS :
  ShallowWaterReceiptIsFullThreeDimensionalFreeSurfaceNS → ⊥
shallowWaterReceiptIsNotFullThreeDimensionalFreeSurfaceNS ()

data FiniteStableRunProvesPhysicalCalibration : Set where
finiteStableRunDoesNotProvePhysicalCalibration :
  FiniteStableRunProvesPhysicalCalibration → ⊥
finiteStableRunDoesNotProvePhysicalCalibration ()

data HydrostaticHullLoadProxyIsStructuralFEA : Set where
hydrostaticHullLoadProxyIsNotStructuralFEA :
  HydrostaticHullLoadProxyIsStructuralFEA → ⊥
hydrostaticHullLoadProxyIsNotStructuralFEA ()

data DomainMassChangeIsClosedDomainConservationProof : Set where
domainMassChangeIsNotClosedDomainConservationProof :
  DomainMassChangeIsClosedDomainConservationProof → ⊥
domainMassChangeIsNotClosedDomainConservationProof ()

data DashiCFDNumericalRunProvesNavierStokesClay : Set where
dashicfdRunDoesNotProveNavierStokesClay :
  DashiCFDNumericalRunProvesNavierStokesClay → ⊥
dashicfdRunDoesNotProveNavierStokesClay ()
