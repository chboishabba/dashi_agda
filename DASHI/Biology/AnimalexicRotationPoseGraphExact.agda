module DASHI.Biology.AnimalexicRotationPoseGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED MULTI-KEYFRAME ROTATION POSE GRAPH
------------------------------------------------------------------------

record RotationPoseGraphReceipt : Set where
  constructor rotation-pose-graph-receipt
  field
    runtimeReference : String
    firstFrameAnchored : Bool
    relativeRotationConstraintsRequired : Bool
    positiveConstraintWeightsRequired : Bool
    provenanceRequiredPerConstraint : Bool
    connectivityRequired : Bool
    deterministicInitializationImplemented : Bool
    chordalAveragingImplemented : Bool
    projectionBackToSO3Implemented : Bool
    angularResidualMeasured : Bool
    inconsistentLoopCanAbstain : Bool
    translationOptimizationPerformed : Bool
    fullVIOOptimizationPaid : Bool

open RotationPoseGraphReceipt public

currentRotationPoseGraphReceipt : RotationPoseGraphReceipt
currentRotationPoseGraphReceipt =
  rotation-pose-graph-receipt
    "chboishabba/animalexic/scripts/rotation_pose_graph.py"
    true true true true true true true true true true false false

record RotationPoseGraphSyntheticReceipt : Set where
  constructor rotation-pose-graph-synthetic-receipt
  field
    consistentChainLoopAngularRMS : String
    inconsistentLoopAngularRMS : String
    disconnectedGraphRejected : Bool
    exactRepositoryCheckoutExecutionPaid : Bool

open RotationPoseGraphSyntheticReceipt public

currentRotationPoseGraphSyntheticReceipt : RotationPoseGraphSyntheticReceipt
currentRotationPoseGraphSyntheticReceipt =
  rotation-pose-graph-synthetic-receipt "0.0 deg" "20.000000000000018 deg" true false

data RotationGraphCandidateImpliesFullVIOPermission : Set where

data LowAngularResidualImpliesOrientationTruthPermission : Set where

data LoopRotationConstraintImpliesLoopIdentityPermission : Set where

rotationGraphDoesNotPayFullVIO :
  RotationGraphCandidateImpliesFullVIOPermission → ⊥
rotationGraphDoesNotPayFullVIO ()

lowAngularResidualDoesNotPayOrientationTruth :
  LowAngularResidualImpliesOrientationTruthPermission → ⊥
lowAngularResidualDoesNotPayOrientationTruth ()

loopRotationConstraintDoesNotPayLoopIdentity :
  LoopRotationConstraintImpliesLoopIdentityPermission → ⊥
loopRotationConstraintDoesNotPayLoopIdentity ()

record RotationPoseGraphRoadmapStatus : Set where
  constructor rotation-pose-graph-roadmap-status
  field
    rotationGraphCandidateImplemented : Bool
    angularLoopResidualGateImplemented : Bool
    syntheticRotationGraphProbePaid : Bool
    jointSE3OptimizationPaid : Bool
    jointVisualInertialStateOptimizationPaid : Bool
    realPhoneLoopClosureValidated : Bool

open RotationPoseGraphRoadmapStatus public

currentRotationPoseGraphRoadmapStatus : RotationPoseGraphRoadmapStatus
currentRotationPoseGraphRoadmapStatus =
  rotation-pose-graph-roadmap-status true true true false false false
