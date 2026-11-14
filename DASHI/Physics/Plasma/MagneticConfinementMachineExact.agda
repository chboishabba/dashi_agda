module DASHI.Physics.Plasma.MagneticConfinementMachineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Plasma.MagneticTopologyHyperfabricExact as Plasma
import DASHI.Physics.Plasma.MHDMaxwellLorentzReductionBidiExact as Stack

------------------------------------------------------------------------
-- MAGNETIC-CONFINEMENT MACHINE KERNEL
--
-- This is deliberately device-agnostic.  Tokamaks and stellarators are
-- specialisations of the same state-indexed SI / U(1)-EM / Lorentz / MHD
-- stack.  Equilibrium, stability, transport, kinetic closure and fusion
-- performance remain separate receipts.
------------------------------------------------------------------------

data ConfinementGeometry : Set where
  axisymmetricToroidal : ConfinementGeometry
  threeDimensionalToroidal : ConfinementGeometry

record MagneticConfinementState : Set₁ where
  constructor magnetic-confinement-state
  field
    voxel : Plasma.PlasmaHypervoxel
    lawStack : Stack.MagnetizedPlasmaLawStack
    geometry : ConfinementGeometry

    majorRadius : SI.Measurement SI.Length SI.unitScale
    minorRadius : SI.Measurement SI.Length SI.unitScale
    magneticField : SI.Measurement SI.MagneticFluxDensity SI.unitScale
    plasmaCurrent : SI.Measurement SI.Current SI.unitScale
    pressure : SI.Measurement SI.Pressure SI.unitScale
    temperature : SI.Measurement SI.Temperature SI.unitScale
    density : SI.Measurement SI.Density SI.unitScale
    energyConfinementTime : SI.Measurement SI.Time SI.unitScale

    beta : SI.Measurement SI.Dimensionless SI.unitScale
    safetyOrRotationalTransform : SI.Measurement SI.Dimensionless SI.unitScale

    configurationReference : String

open MagneticConfinementState public

record EquilibriumReceipt (state : MagneticConfinementState) : Set₁ where
  constructor equilibrium-receipt
  field
    nestedFluxSurfaceReceipt : Set
    mhdForceBalanceReceipt : Set
    pressureProfileReceipt : Set
    currentProfileReceipt : Set
    boundaryConditionReceipt : Set
    reconstructionAuthority : Authority.ArtifactAuthorityBoundary
    equilibriumReference : String

open EquilibriumReceipt public

record StabilityReceipt (state : MagneticConfinementState) : Set₁ where
  constructor stability-receipt
  field
    idealMHDStabilityReceipt : Set
    resistiveMHDStabilityReceipt : Set
    kineticOrMicrostabilityReceipt : Set
    stabilityReference : String

open StabilityReceipt public

record TransportReceipt (state : MagneticConfinementState) : Set₁ where
  constructor transport-receipt
  field
    collisionalTransportReceipt : Set
    neoclassicalTransportReceipt : Set
    turbulentTransportReceipt : Set
    energeticParticleConfinementReceipt : Set
    transportReference : String

open TransportReceipt public

record FusionPerformanceReceipt (state : MagneticConfinementState) : Set₁ where
  constructor fusion-performance-receipt
  field
    fuelSpeciesReceipt : Set
    densityTemperatureConfinementReceipt : Set
    reactionRateReceipt : Set
    alphaOrProductHeatingReceipt : Set
    netPowerAccountingReceipt : Set
    performanceAuthority : Authority.ArtifactAuthorityBoundary
    performanceReference : String

open FusionPerformanceReceipt public

------------------------------------------------------------------------
-- BIDI firewalls.
------------------------------------------------------------------------

record MagneticConfinementBoundary : Set where
  constructor magnetic-confinement-boundary
  field
    canonicalSIOwnerReused : Bool
    canonicalU1MaxwellLorentzMHDStackReused : Bool

    siTypingAloneProvesEquilibrium : Bool
    siTypingAloneProvesEquilibriumIsFalse :
      siTypingAloneProvesEquilibrium ≡ false

    mhdEquilibriumAloneProvesKineticTransport : Bool
    mhdEquilibriumAloneProvesKineticTransportIsFalse :
      mhdEquilibriumAloneProvesKineticTransport ≡ false

    nestedFluxSurfacesAloneProveStability : Bool
    nestedFluxSurfacesAloneProveStabilityIsFalse :
      nestedFluxSurfacesAloneProveStability ≡ false

    confinementTopologyAloneProvesFusion : Bool
    confinementTopologyAloneProvesFusionIsFalse :
      confinementTopologyAloneProvesFusion ≡ false

    empiricalPerformanceRequiresArtifactAuthority : Bool
    empiricalPerformanceRequiresArtifactAuthorityIsTrue :
      empiricalPerformanceRequiresArtifactAuthority ≡ true

canonicalMagneticConfinementBoundary : MagneticConfinementBoundary
canonicalMagneticConfinementBoundary =
  magnetic-confinement-boundary
    true true
    false refl
    false refl
    false refl
    false refl
    true refl
