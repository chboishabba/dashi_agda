module DASHI.Physics.Optics.LESOpticalSurrogateEscalationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.SurrogateCalibration as LES
import DASHI.Environment.LatentDepthFormalism as Latent
import DASHI.Physics.Optics.AsphericCausticManipulationExact as Caustic
import DASHI.Physics.Optics.InverseCausticNumericalProducerExact as Numerical

------------------------------------------------------------------------
-- LES SURROGATE ESCALATION / OPTICAL INVERSE DESIGN
--
-- LES already owns the rule that reduced models amortise authoritative
-- simulation rather than replace it: out-of-support, high-residual,
-- high-uncertainty, conservation-failing, or policy-critical cases escalate.
-- This module instantiates that architecture around optical candidate search.
------------------------------------------------------------------------

record OpticalSurrogateSearchReceipt : Set₁ where
  constructor optical-surrogate-search-receipt
  field
    calibration : LES.CalibrationReceipt
    useReceipt : LES.SurrogateUseReceipt
    candidateSearchDescription : String
    opticalOutputsPredicted : String
    candidateArtifactDigest : String

open OpticalSurrogateSearchReceipt public

record EscalatedAuthoritativeOpticalReceipt
    {SourceModel TargetPattern SourceRay SurfacePoint TargetPoint Normal Flux Scalar : Set}
    {problem : Numerical.InverseCausticProblem SourceModel TargetPattern}
    {surface : Caustic.OpticalSurfaceGeometry SurfacePoint Normal}
    {rayMap : Caustic.CausticRayMap SourceRay SurfacePoint TargetPoint Flux}
    {algebra : Numerical.ResidualAlgebra Scalar}
    {candidate : Numerical.NumericalInverseCausticCandidate {Scalar = Scalar} problem surface rayMap}
    {thresholds : Numerical.NumericalAdmissionThresholds algebra}
    (surrogate : OpticalSurrogateSearchReceipt)
    (authoritative : Numerical.CertifiedInverseCausticNumericalSolution algebra candidate thresholds) : Set₁ where
  constructor escalated-authoritative-optical-receipt
  field
    surrogateResultingLane : Latent.ModelLane
    surrogateLaneIsRetained :
      surrogateResultingLane ≡ LES.resultingLane (useReceipt surrogate)
    authoritativeSolution :
      Numerical.CertifiedInverseCausticNumericalSolution algebra candidate thresholds
    authoritativeSolutionIsSameObject : authoritativeSolution ≡ authoritative
    escalationOrVerificationReading : String

open EscalatedAuthoritativeOpticalReceipt public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data SurrogatePredictionIsCertifiedInverseDesign : Set where
surrogatePredictionIsNotCertifiedInverseDesign :
  SurrogatePredictionIsCertifiedInverseDesign → ⊥
surrogatePredictionIsNotCertifiedInverseDesign ()

data InsideTrainingSupportImpliesZeroOpticalResidual : Set where
insideTrainingSupportDoesNotImplyZeroOpticalResidual :
  InsideTrainingSupportImpliesZeroOpticalResidual → ⊥
insideTrainingSupportDoesNotImplyZeroOpticalResidual ()

data AuthoritativeOpticalSolveImpliesSiteDeploymentApproval : Set where
authoritativeOpticalSolveDoesNotImplySiteDeploymentApproval :
  AuthoritativeOpticalSolveImpliesSiteDeploymentApproval → ⊥
authoritativeOpticalSolveDoesNotImplySiteDeploymentApproval ()
