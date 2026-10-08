module DASHI.Physics.Plasma.StellaratorConfinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement

------------------------------------------------------------------------
-- STELLARATOR SPECIALISATION
--
-- The rotational transform is supplied by a genuinely three-dimensional
-- external magnetic-field system.  A net toroidal plasma current is therefore
-- not required to generate the confining twist, though bootstrap/induced
-- currents may still be present and must be handled by the state model.
------------------------------------------------------------------------

record StellaratorState : Set₁ where
  constructor stellarator-state
  field
    confined : Confinement.MagneticConfinementState
    geometryIsThreeDimensionalToroidal :
      Confinement.geometry confined ≡ Confinement.threeDimensionalToroidal

    externalThreeDimensionalCoilReceipt : Set
    rotationalTransformFromExternalFieldReceipt : Set
    vacuumFieldReceipt : Set
    coilToFluxSurfaceSameObjectReceipt : Set
    divertorOrBoundaryControlReceipt : Set

    stellaratorReference : String

open StellaratorState public

record StellaratorEquilibriumReceipt (state : StellaratorState) : Set₁ where
  constructor stellarator-equilibrium-receipt
  field
    genericEquilibrium : Confinement.EquilibriumReceipt (confined state)
    threeDimensionalMHDEquilibriumReceipt : Set
    rotationalTransformProfileReceipt : Set
    magneticSurfaceReceipt : Set
    bootstrapCurrentReceipt : Set
    magneticReconstructionAuthority : Authority.ArtifactAuthorityBoundary
    equilibriumReference : String

open StellaratorEquilibriumReceipt public

record StellaratorOptimizationReceipt (state : StellaratorState) : Set₁ where
  constructor stellarator-optimization-receipt
  field
    equilibrium : StellaratorEquilibriumReceipt state
    stability : Confinement.StabilityReceipt (confined state)
    transport : Confinement.TransportReceipt (confined state)
    neoclassicalOptimizationReceipt : Set
    energeticParticleOrbitReceipt : Set
    coilRealizabilityReceipt : Set
    optimizationReference : String

open StellaratorOptimizationReceipt public

------------------------------------------------------------------------
-- BIDI firewalls.
------------------------------------------------------------------------

record StellaratorBoundary : Set where
  constructor stellarator-boundary
  field
    externalCoilsSupplyConfiningRotationalTransform : Bool
    externalCoilsSupplyConfiningRotationalTransformIsTrue :
      externalCoilsSupplyConfiningRotationalTransform ≡ true

    netToroidalPlasmaCurrentRequiredForConfiningTwist : Bool
    netToroidalPlasmaCurrentRequiredForConfiningTwistIsFalse :
      netToroidalPlasmaCurrentRequiredForConfiningTwist ≡ false

    axisymmetryRequiredByDefinition : Bool
    axisymmetryRequiredByDefinitionIsFalse :
      axisymmetryRequiredByDefinition ≡ false

    steadyStateOperationCompatibleByTopology : Bool
    steadyStateOperationCompatibleByTopologyIsTrue :
      steadyStateOperationCompatibleByTopology ≡ true

    threeDimensionalMHDAloneProvesTransport : Bool
    threeDimensionalMHDAloneProvesTransportIsFalse :
      threeDimensionalMHDAloneProvesTransport ≡ false

    stellaratorTopologyAloneProvesFusionPerformance : Bool
    stellaratorTopologyAloneProvesFusionPerformanceIsFalse :
      stellaratorTopologyAloneProvesFusionPerformance ≡ false

canonicalStellaratorBoundary : StellaratorBoundary
canonicalStellaratorBoundary =
  stellarator-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl

stellaratorPrimaryReference : String
stellaratorPrimaryReference =
  "Max-Planck-Institut fuer Plasmaphysik stellarator/Wendelstein 7-X public technical material; external 3-D coils generate the field-line twist without requiring net longitudinal plasma current"
