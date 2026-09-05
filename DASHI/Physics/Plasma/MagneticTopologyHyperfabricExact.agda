module DASHI.Physics.Plasma.MagneticTopologyHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MAGNETIZED-PLASMA HYPERFABRIC
--
-- The plasma state is a dependent fibre over a material/kinematic base.  The
-- magnetic topology is not flattened into a scalar tag: it remains an explicit
-- fibre coordinate together with fields/current/flux information.
------------------------------------------------------------------------

record PlasmaBase : Set₁ where
  constructor plasma-base
  field
    Position Time Density Temperature BulkVelocity Pressure : Set
    baseReference : String

open PlasmaBase public

record MagneticFibre (base : PlasmaBase) : Set₁ where
  constructor magnetic-fibre
  field
    ElectricField MagneticField CurrentDensity MagneticFlux : Set
    FieldLineTopology MagneticHelicity GeneralizedOhmResidual : Set
    electromagneticReference : String
    topologyReference : String

open MagneticFibre public

record PlasmaHypervoxel : Set₁ where
  constructor plasma-hypervoxel
  field
    base : PlasmaBase
    fibre : MagneticFibre base

open PlasmaHypervoxel public

PlasmaHyperfabric : Set₁
PlasmaHyperfabric = PlasmaHypervoxel

------------------------------------------------------------------------
-- A consumer that observes only thermodynamic coordinates cannot reconstruct
-- the magnetic-topology fibre by definition.
------------------------------------------------------------------------

record PlasmaProjectionBoundary : Set where
  constructor plasma-projection-boundary
  field
    temperatureAloneDeterminesTopology : Bool
    temperatureAloneDeterminesTopologyIsFalse :
      temperatureAloneDeterminesTopology ≡ false

    densityAloneDeterminesReconnection : Bool
    densityAloneDeterminesReconnectionIsFalse :
      densityAloneDeterminesReconnection ≡ false

    topologyIsIndependentFibreCoordinate : Bool
    topologyIsIndependentFibreCoordinateIsTrue :
      topologyIsIndependentFibreCoordinate ≡ true

canonicalPlasmaProjectionBoundary : PlasmaProjectionBoundary
canonicalPlasmaProjectionBoundary =
  plasma-projection-boundary false refl false refl true refl
