module DASHI.Biology.AnimalexicFixedRotationVISmootherExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FIXED-ROTATION MULTI-KEYFRAME VISUAL-INERTIAL POSITION/VELOCITY SMOOTHER
------------------------------------------------------------------------

record FixedRotationVISmootherReceipt : Set where
  constructor fixed-rotation-vi-smoother-receipt
  field
    runtimeReference : String
    rotationsSuppliedAndFixed : Bool
    inertialPositionDeltaConstraintImplemented : Bool
    inertialVelocityDeltaConstraintImplemented : Bool
    initialVelocityTermRetainedInPositionEquation : Bool
    visualTranslationConstraintsImplemented : Bool
    positionAnchorRequired : Bool
    velocityAnchorRequired : Bool
    inertialConnectivityRequired : Bool
    fullAnchoredRankRequired : Bool
    globalLeastSquaresSolveImplemented : Bool
    residualGateCanAbstain : Bool
    rotationsJointlyOptimized : Bool
    biasesJointlyOptimized : Bool
    fullNonlinearVIOPaid : Bool

open FixedRotationVISmootherReceipt public

currentFixedRotationVISmootherReceipt : FixedRotationVISmootherReceipt
currentFixedRotationVISmootherReceipt =
  fixed-rotation-vi-smoother-receipt
    "chboishabba/animalexic/scripts/linear_visual_inertial_smoother.py"
    true true true true true true true true true true true false false false

record FixedRotationVISyntheticReceipt : Set where
  constructor fixed-rotation-vi-synthetic-receipt
  field
    constantVelocityChainRecovered : Bool
    controlledLinearRMS : String
    inconsistentVisualConstraintCanAbstain : Bool
    disconnectedInertialGraphRejected : Bool
    exactRepositoryCheckoutExecutionPaid : Bool

open FixedRotationVISyntheticReceipt public

currentFixedRotationVISyntheticReceipt : FixedRotationVISyntheticReceipt
currentFixedRotationVISyntheticReceipt =
  fixed-rotation-vi-synthetic-receipt
    true "3.9093549504695504e-16" true true false

data FixedRotationVISmootherImpliesFullVIOPermission : Set where

data LowLinearResidualImpliesTrajectoryTruthPermission : Set where

data FixedRotationsImpliesRotationOptimizationPermission : Set where

fixedRotationSmootherDoesNotPayFullVIO :
  FixedRotationVISmootherImpliesFullVIOPermission → ⊥
fixedRotationSmootherDoesNotPayFullVIO ()

lowLinearResidualDoesNotPayTrajectoryTruth :
  LowLinearResidualImpliesTrajectoryTruthPermission → ⊥
lowLinearResidualDoesNotPayTrajectoryTruth ()

fixedRotationsDoNotPayRotationOptimization :
  FixedRotationsImpliesRotationOptimizationPermission → ⊥
fixedRotationsDoNotPayRotationOptimization ()

record FixedRotationVIRoadmapStatus : Set where
  constructor fixed-rotation-vi-roadmap-status
  field
    jointPositionVelocityCandidateImplemented : Bool
    visualAndInertialConstraintsShareOneSolve : Bool
    syntheticProbePaid : Bool
    jointRotationPositionVelocityOptimizationPaid : Bool
    biasStateOptimizationPaid : Bool
    covariancePropagationPaid : Bool
    realHandheldTrajectoryValidated : Bool

open FixedRotationVIRoadmapStatus public

currentFixedRotationVIRoadmapStatus : FixedRotationVIRoadmapStatus
currentFixedRotationVIRoadmapStatus =
  fixed-rotation-vi-roadmap-status true true true false false false false
