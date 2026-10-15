module DASHI.Physics.Quantum.MagnetocaloricQuantumStatMechConsumerExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Laws.QuantumFieldLaws as Quantum
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo
import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial as MCE

------------------------------------------------------------------------
-- Quantum/statistical-mechanical consumer for magnetocaloric response.
--
-- The chain Hamiltonian -> ensemble/state weighting -> thermodynamic free
-- energy -> M/S/C is evidence-bearing.  A Hamiltonian carrier by itself does
-- not provide a partition function, an equilibrium ensemble, a derivative, or
-- a calibrated material response.
------------------------------------------------------------------------

record QuantumMagnetocaloricProvider
  (Q : Quantum.QuantumKinematics)
  (D : Quantum.QuantumDynamics Q)
  (E : Thermo.StatisticalEnsemble)
  (M : MCE.MagnetocaloricMaterial)
  (R : MCE.MagnetocaloricResponse M) : Set₁ where
  open Quantum.QuantumKinematics Q
  open Quantum.QuantumDynamics D
  open Thermo.StatisticalEnsemble E
  open MCE.MagnetocaloricMaterial M
  field
    hamiltonian : Hamiltonian
    quantumState : State
    ensembleParameter : Parameter
    materialState : MaterialState

    FreeEnergy : Set
    PartitionEvidence : Set
    EquilibriumEvidence : Set
    QuantumMaterialIdentification : Set

    freeEnergy : FreeEnergy
    partitionEvidence : PartitionEvidence
    equilibriumEvidence : EquilibriumEvidence
    quantumMaterialIdentification : QuantumMaterialIdentification

    MagnetisationProjection : Set
    EntropyProjection : Set
    HeatCapacityProjection : Set

    magnetisationProjection : MagnetisationProjection
    entropyProjection : EntropyProjection
    heatCapacityProjection : HeatCapacityProjection

    ResponseCompatible : Set
    responseCompatible : ResponseCompatible

record QuantumMagnetocaloricDerivativeBridge
  {M : MCE.MagnetocaloricMaterial}
  (R : MCE.MagnetocaloricResponse M) : Set₁ where
  field
    FreeEnergyDerivativeWrtField : Set
    FreeEnergyDerivativeWrtTemperature : Set
    HeatCapacityDerivativeLaw : Set
    RegularityRegime : Set

    fieldDerivativeLaw : FreeEnergyDerivativeWrtField
    temperatureDerivativeLaw : FreeEnergyDerivativeWrtTemperature
    heatCapacityDerivativeLaw : HeatCapacityDerivativeLaw
    regularityRegime : RegularityRegime

record QuantumMagnetocaloricAuthorityBoundary : Set where
  constructor quantum-magnetocaloric-authority-boundary
  field
    quantumCarrierIsNotCalibratedMaterial : Bool
    HamiltonianDoesNotSupplyPartitionFunction : Bool
    partitionFunctionNeedsEnsembleAndNormalisation : Bool
    freeEnergyDerivativeNeedsRegularity : Bool
    firstOrderTransitionNeedsSeparateTreatment : Bool
    quantumProjectionDoesNotProveAMRCooling : Bool
    finiteQuantumModelDoesNotProveBulkThermodynamicLimit : Bool

canonicalQuantumMagnetocaloricAuthorityBoundary : QuantumMagnetocaloricAuthorityBoundary
canonicalQuantumMagnetocaloricAuthorityBoundary =
  quantum-magnetocaloric-authority-boundary true true true true true true true
