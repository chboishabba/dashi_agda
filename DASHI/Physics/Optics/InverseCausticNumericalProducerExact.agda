module DASHI.Physics.Optics.InverseCausticNumericalProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.AsphericCausticManipulationExact as Caustic
import DASHI.Physics.Optics.CausticFreeformSourceAtlasExact as Sources

------------------------------------------------------------------------
-- NUMERICAL PRODUCER / FORMAL ADMISSION BOUNDARY
--
-- Meyron-Merigot-Thibert and Zhou-Sun-Deng-Zhang motivate constructive
-- inverse-design producers, but this Agda owner does not pretend to perform
-- the numerical optimisation.  Instead it specifies the exact packet a
-- numerical solver must return before a candidate is admitted downstream.
--
-- External solver output is therefore not promoted by mere serialization:
-- residuals, source/target identity, ray-map identity, and surface identity
-- remain explicit proof obligations.
------------------------------------------------------------------------

record ResidualAlgebra (Scalar : Set) : Set₁ where
  constructor residual-algebra
  field
    zero : Scalar
    _≤_ : Scalar → Scalar → Set

open ResidualAlgebra public

record InverseCausticProblem
    (SourceModel TargetPattern : Set) : Set₁ where
  constructor inverse-caustic-problem
  field
    sourceModel : SourceModel
    targetPattern : TargetPattern
    apertureSpecification : String
    opticalRegime : String
    boundaryConditions : String
    sourceAuthority : Sources.CausticFreeformSourceBoundary

open InverseCausticProblem public

record NumericalInverseCausticCandidate
    {SourceModel TargetPattern SourceRay SurfacePoint TargetPoint Normal Flux Scalar : Set}
    (problem : InverseCausticProblem SourceModel TargetPattern)
    (surface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal)
    (rayMap : Caustic.CausticRayMap SourceRay SurfacePoint TargetPoint Flux) : Set₁ where
  constructor numerical-inverse-caustic-candidate
  field
    solverName : String
    solverVersionOrCommit : String
    solverConfiguration : String

    retainedSourceModel : SourceModel
    retainedSourceModelIsSameObject : retainedSourceModel ≡ sourceModel problem

    retainedTargetPattern : TargetPattern
    retainedTargetPatternIsSameObject : retainedTargetPattern ≡ targetPattern problem

    retainedSurface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal
    retainedSurfaceIsSameObject : retainedSurface ≡ surface

    retainedRayMap : Caustic.CausticRayMap SourceRay SurfacePoint TargetPoint Flux
    retainedRayMapIsSameObject : retainedRayMap ≡ rayMap

    fluxResidual : Scalar
    integrabilityResidual : Scalar
    targetPatternResidual : Scalar
    boundaryResidual : Scalar
    visibilityResidual : Scalar

    numericalArtifactDigest : String
    numericalRunReceipt : String

open NumericalInverseCausticCandidate public

record NumericalAdmissionThresholds
    {Scalar : Set}
    (algebra : ResidualAlgebra Scalar) : Set where
  constructor numerical-admission-thresholds
  field
    maxFluxResidual : Scalar
    maxIntegrabilityResidual : Scalar
    maxTargetPatternResidual : Scalar
    maxBoundaryResidual : Scalar
    maxVisibilityResidual : Scalar

open NumericalAdmissionThresholds public

record CertifiedInverseCausticNumericalSolution
    {SourceModel TargetPattern SourceRay SurfacePoint TargetPoint Normal Flux Scalar : Set}
    {problem : InverseCausticProblem SourceModel TargetPattern}
    {surface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal}
    {rayMap : Caustic.CausticRayMap SourceRay SurfacePoint TargetPoint Flux}
    (algebra : ResidualAlgebra Scalar)
    (candidate : NumericalInverseCausticCandidate
      {Scalar = Scalar} problem surface rayMap)
    (thresholds : NumericalAdmissionThresholds algebra) : Set₁ where
  constructor certified-inverse-caustic-numerical-solution
  field
    fluxResidualAdmissible :
      _≤_ algebra (fluxResidual candidate) (maxFluxResidual thresholds)
    integrabilityResidualAdmissible :
      _≤_ algebra (integrabilityResidual candidate) (maxIntegrabilityResidual thresholds)
    targetPatternResidualAdmissible :
      _≤_ algebra (targetPatternResidual candidate) (maxTargetPatternResidual thresholds)
    boundaryResidualAdmissible :
      _≤_ algebra (boundaryResidual candidate) (maxBoundaryResidual thresholds)
    visibilityResidualAdmissible :
      _≤_ algebra (visibilityResidual candidate) (maxVisibilityResidual thresholds)

    fluxConservationEvidence : String
    normalIntegrabilityEvidence : String
    opticalLawEvidence : String
    convergenceOrTerminationEvidence : String

open CertifiedInverseCausticNumericalSolution public

------------------------------------------------------------------------
-- Promotion into the existing design layer remains explicit.  The numerical
-- solution does not become a freeform design receipt without an adapter that
-- preserves the same surface and ray map.
------------------------------------------------------------------------

record NumericalSolutionDesignWeld
    {SourceModel TargetPattern SourceRay SurfacePoint TargetPoint Normal Flux Scalar : Set}
    {problem : InverseCausticProblem SourceModel TargetPattern}
    {surface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal}
    {rayMap : Caustic.CausticRayMap SourceRay SurfacePoint TargetPoint Flux}
    {algebra : ResidualAlgebra Scalar}
    {candidate : NumericalInverseCausticCandidate {Scalar = Scalar} problem surface rayMap}
    {thresholds : NumericalAdmissionThresholds algebra}
    (solution : CertifiedInverseCausticNumericalSolution algebra candidate thresholds)
    (design : Caustic.FreeformCausticDesignReceipt surface rayMap) : Set₁ where
  constructor numerical-solution-design-weld
  field
    sameSurfaceReading : String
    sameRayMapReading : String
    numericalResidualsPayDesignObligations : String

open NumericalSolutionDesignWeld public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data SolverOutputIsCertifiedByExistence : Set where
solverOutputIsNotCertifiedByExistence : SolverOutputIsCertifiedByExistence → ⊥
solverOutputIsNotCertifiedByExistence ()

data LowTargetErrorImpliesIntegrableSurface : Set where
lowTargetErrorDoesNotImplyIntegrableSurface : LowTargetErrorImpliesIntegrableSurface → ⊥
lowTargetErrorDoesNotImplyIntegrableSurface ()

data NumericalConvergenceImpliesPhysicalManufacturability : Set where
numericalConvergenceDoesNotImplyPhysicalManufacturability :
  NumericalConvergenceImpliesPhysicalManufacturability → ⊥
numericalConvergenceDoesNotImplyPhysicalManufacturability ()
