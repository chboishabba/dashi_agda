module DASHI.Physics.Optics.LESOpticalNumericalWitnessCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.CertifiedValidationGovernanceExact as LESGovernance
import DASHI.Physics.Optics.InverseCausticNumericalProducerExact as Numerical

------------------------------------------------------------------------
-- LES / OPTICS CROSS-POLLINATION
--
-- LES already distinguishes runtime evidence from proof-bearing promotion.
-- The inverse-caustic lane has the same architecture: an external numerical
-- producer emits a candidate and residual packet; admission is a separate
-- proof obligation.  This bridge records that common contract without making
-- LES itself the optical solver or the optics module a deployment planner.
------------------------------------------------------------------------

record LESStyleNumericalWitnessContract : Set₁ where
  constructor les-style-numerical-witness-contract
  field
    runtimeProducer : String
    producedArtifact : String
    artifactDigest : String
    validationProgramme : String
    uncertaintyDisclosure : String
    missingDataDisclosure : String
    promotionBoundary : String

open LESStyleNumericalWitnessContract public

record GovernedOpticalNumericalWitness
    {SourceModel TargetPattern SourceRay SurfacePoint TargetPoint Normal Flux Scalar : Set}
    {problem : Numerical.InverseCausticProblem SourceModel TargetPattern}
    {surface : DASHI.Physics.Optics.AsphericCausticManipulationExact.OpticalSurfaceGeometry SurfacePoint Normal}
    {rayMap : DASHI.Physics.Optics.AsphericCausticManipulationExact.CausticRayMap SourceRay SurfacePoint TargetPoint Flux}
    {algebra : Numerical.ResidualAlgebra Scalar}
    {candidate : Numerical.NumericalInverseCausticCandidate {Scalar = Scalar} problem surface rayMap}
    {thresholds : Numerical.NumericalAdmissionThresholds algebra}
    (solution : Numerical.CertifiedInverseCausticNumericalSolution algebra candidate thresholds) : Set₁ where
  constructor governed-optical-numerical-witness
  field
    lesContract : LESStyleNumericalWitnessContract
    retainedSolution : Numerical.CertifiedInverseCausticNumericalSolution algebra candidate thresholds
    retainedSolutionIsSameObject : retainedSolution ≡ solution
    deploymentContext : String
    downstreamValidationProgramme : String
    downstreamGovernanceReceipt : String

open GovernedOpticalNumericalWitness public

------------------------------------------------------------------------
-- Exact non-promotion boundaries inherited from both architectures.
------------------------------------------------------------------------

data RuntimeWitnessImpliesDeploymentPermission : Set where
runtimeWitnessDoesNotImplyDeploymentPermission : RuntimeWitnessImpliesDeploymentPermission → ⊥
runtimeWitnessDoesNotImplyDeploymentPermission ()

data OpticalResidualAdmissionImpliesEcologicalSiteSuitability : Set where
opticalResidualAdmissionDoesNotImplyEcologicalSiteSuitability :
  OpticalResidualAdmissionImpliesEcologicalSiteSuitability → ⊥
opticalResidualAdmissionDoesNotImplyEcologicalSiteSuitability ()

data LESGovernanceIsNumericalOpticalSolver : Set where
lesGovernanceIsNotNumericalOpticalSolver : LESGovernanceIsNumericalOpticalSolver → ⊥
lesGovernanceIsNotNumericalOpticalSolver ()
