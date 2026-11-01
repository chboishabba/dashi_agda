module DASHI.Biology.MolecularMechanicsRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Biology.MolecularMechanicsPotentialBridge as Abstract
import DASHI.Biology.ConcreteProteinMolecularMechanics as Concrete
import DASHI.Biology.MolecularMechanicsForcesDynamics as Dynamics
import DASHI.Biology.BoltzmannConformationalEnsemble as Ensemble
import DASHI.Biology.MolecularMechanicsCartesianProduction as Cartesian
import DASHI.Biology.CertifiedMolecularNumericsParameters as Certified
import DASHI.Biology.MolecularMechanicsSamplingAlgorithms as Sampling

------------------------------------------------------------------------
-- One compact import surface for the molecular-mechanics tranche.

record MolecularMechanicsTrancheStatus : Set where
  field
    abstractPotentialBridgePresent : Bool
    concreteFloatCarrierPresent : Bool
    finiteProteinConfigurationPresent : Bool
    literalFiveTermPotentialPresent : Bool
    explicitRadialForcesPresent : Bool
    fullCartesianAngleFormulaPresent : Bool
    fullCartesianTorsionFormulaPresent : Bool
    singularChartGuardsPresent : Bool
    atomwiseForceAggregationPresent : Bool
    completeVelocityVerletPresent : Bool
    newtonianDynamicsPresent : Bool
    langevinDynamicsPresent : Bool
    finiteBoltzmannEnsemblePresent : Bool
    intervalCertificationArchitecturePresent : Bool
    parameterImportSchemaPresent : Bool
    demonstrationParameterSetPresent : Bool
    metropolisHastingsPresent : Bool
    replicaExchangePresent : Bool
    umbrellaSamplingPresent : Bool
    compilerCheckStillOpen : Bool
    rigorousOutwardRoundingStillOpen : Bool
    thirdPartyParameterImportStillOpen : Bool
    equilibriumConvergenceStillOpen : Bool
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
    ; fullCartesianAngleFormulaPresent = true
    ; fullCartesianTorsionFormulaPresent = true
    ; singularChartGuardsPresent = true
    ; atomwiseForceAggregationPresent = true
    ; completeVelocityVerletPresent = true
    ; newtonianDynamicsPresent = true
    ; langevinDynamicsPresent = true
    ; finiteBoltzmannEnsemblePresent = true
    ; intervalCertificationArchitecturePresent = true
    ; parameterImportSchemaPresent = true
    ; demonstrationParameterSetPresent = true
    ; metropolisHastingsPresent = true
    ; replicaExchangePresent = true
    ; umbrellaSamplingPresent = true
    ; compilerCheckStillOpen = true
    ; rigorousOutwardRoundingStillOpen = true
    ; thirdPartyParameterImportStillOpen = true
    ; equilibriumConvergenceStillOpen = true
    ; experimentalValidationStillOpen = true
    ; statusReading =
        "The executable finite molecular-mechanics stack now includes Cartesian angle/torsion formulas, atomwise force aggregation, complete velocity Verlet, interval-certification interfaces, parameter schemas, and concrete sampling kernels. Compiler verification, outward-rounded backend proofs, sourced third-party force-field tables, equilibrium convergence, and experimental validation remain open."
    }

canonicalFullCartesianAngleFormulaPresent :
  fullCartesianAngleFormulaPresent
    canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalFullCartesianAngleFormulaPresent = refl

canonicalFullCartesianTorsionFormulaPresent :
  fullCartesianTorsionFormulaPresent
    canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalFullCartesianTorsionFormulaPresent = refl

canonicalCompleteVelocityVerletPresent :
  completeVelocityVerletPresent
    canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalCompleteVelocityVerletPresent = refl

canonicalMetropolisHastingsPresent :
  metropolisHastingsPresent
    canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalMetropolisHastingsPresent = refl

canonicalCompilerCheckStillOpen :
  compilerCheckStillOpen canonicalMolecularMechanicsTrancheStatus ≡ true
canonicalCompilerCheckStillOpen = refl

------------------------------------------------------------------------
-- Public availability witnesses.

concretePotentialAvailable :
  Concrete.ProteinConfiguration → Float
concretePotentialAvailable = Concrete.concreteTotalPotential

finitePartitionAvailable :
  Ensemble.ThermodynamicParameters →
  List Ensemble.WeightedConformation →
  Float
finitePartitionAvailable = Ensemble.finitePartitionFunction

aggregateForceAvailable :
  Dynamics.TermwiseForceEvaluation →
  Concrete.ProteinConfiguration →
  Concrete.ProteinForceField
aggregateForceAvailable = Cartesian.aggregateTermwiseForce

completeVerletAvailable :
  Dynamics.VelocityVerletStep →
  List Dynamics.DynamicAtom →
  List Dynamics.DynamicAtom
completeVerletAvailable = Cartesian.completeVelocityVerlet

intervalComparisonAvailable :
  Certified.OutwardRoundedIntervalBackend →
  Certified.Interval →
  Certified.Interval →
  Certified.CertifiedEnergyComparison
intervalComparisonAvailable = Certified.mkCertifiedEnergyComparison
