module DASHI.Biology.MolecularMechanicsRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.MolecularMechanicsPotentialBridge as Abstract
import DASHI.Biology.ConcreteProteinMolecularMechanics as Concrete
import DASHI.Biology.MolecularMechanicsForcesDynamics as Dynamics
import DASHI.Biology.BoltzmannConformationalEnsemble as Ensemble

------------------------------------------------------------------------
-- One compact import surface for the molecular-mechanics tranche.

record MolecularMechanicsTrancheStatus : Set where
  field
    abstractPotentialBridgePresent : Bool
    concreteFloatCarrierPresent : Bool
    finiteProteinConfigurationPresent : Bool
    literalFiveTermPotentialPresent : Bool
    explicitRadialForcesPresent : Bool
    internalCoordinateForceBoundaryPresent : Bool
    newtonianDynamicsPresent : Bool
    langevinDynamicsPresent : Bool
    velocityVerletBoundaryPresent : Bool
    finiteBoltzmannEnsemblePresent : Bool
    continuumConvergenceStillOpen : Bool
    parameterisationStillOpen : Bool
    experimentalValidationStillOpen : Bool
    statusReading : String

open MolecularMechanicsTrancheStatus public

canonicalMolecularMechanicsTrancheStatus :
  MolecularMechanicsTrancheStatus
canonicalMolecularMechanicsTrancheStatus =
  record
    { abstractPotentialBridgePresent = true
    ; concreteFloatCarrierPresent = true
    ; finiteProteinConfigurationPresent = true
    ; literalFiveTermPotentialPresent = true
    ; explicitRadialForcesPresent = true
    ; internalCoordinateForceBoundaryPresent = true
    ; newtonianDynamicsPresent = true
    ; langevinDynamicsPresent = true
    ; velocityVerletBoundaryPresent = true
    ; finiteBoltzmannEnsemblePresent = true
    ; continuumConvergenceStillOpen = true
    ; parameterisationStillOpen = true
    ; experimentalValidationStillOpen = true
    ; statusReading =
        "Executable finite molecular mechanics is present; exact-real analysis, full angle/torsion derivative certification, continuum convergence, force-field calibration, adequate sampling, and experimental validation remain open."
    }

canonicalConcreteFloatCarrierPresent :
  concreteFloatCarrierPresent canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalConcreteFloatCarrierPresent = refl

canonicalFiniteProteinConfigurationPresent :
  finiteProteinConfigurationPresent canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalFiniteProteinConfigurationPresent = refl

canonicalLiteralFiveTermPotentialPresent :
  literalFiveTermPotentialPresent canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalLiteralFiveTermPotentialPresent = refl

canonicalFiniteBoltzmannEnsemblePresent :
  finiteBoltzmannEnsemblePresent canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalFiniteBoltzmannEnsemblePresent = refl

canonicalContinuumConvergenceStillOpen :
  continuumConvergenceStillOpen canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalContinuumConvergenceStillOpen = refl

------------------------------------------------------------------------
-- The imports below force the public definitions to remain available from one
-- checked facade without claiming that the scientific evidence obligations are
-- discharged.

concretePotentialAvailable :
  Concrete.ProteinConfiguration → Float
concretePotentialAvailable = Concrete.concreteTotalPotential

finitePartitionAvailable :
  Ensemble.ThermodynamicParameters →
  List Ensemble.WeightedConformation →
  Float
finitePartitionAvailable = Ensemble.finitePartitionFunction
