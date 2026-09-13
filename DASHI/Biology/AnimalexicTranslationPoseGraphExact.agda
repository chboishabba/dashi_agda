module DASHI.Biology.AnimalexicTranslationPoseGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED MULTI-KEYFRAME TRANSLATION POSE GRAPH
------------------------------------------------------------------------

record TranslationPoseGraphReceipt : Set where
  constructor translation-pose-graph-receipt
  field
    runtimeReference : String
    firstKeyframeAnchored : Bool
    relativeTranslationConstraintsRequired : Bool
    positiveConstraintWeightsRequired : Bool
    provenanceRequiredPerConstraint : Bool
    connectivityRequired : Bool
    fullAnchoredLinearRankRequired : Bool
    leastSquaresGlobalSolveImplemented : Bool
    constraintResidualMeasured : Bool
    residualGateCanAbstain : Bool
    rotationOptimizationPerformed : Bool
    velocityOptimizationPerformed : Bool
    biasOptimizationPerformed : Bool
    fullVIOOptimizationPaid : Bool

open TranslationPoseGraphReceipt public

currentTranslationPoseGraphReceipt : TranslationPoseGraphReceipt
currentTranslationPoseGraphReceipt =
  translation-pose-graph-receipt
    "chboishabba/animalexic/scripts/translation_pose_graph.py"
    true true true true true true true true true false false false false

record TranslationPoseGraphSyntheticReceipt : Set where
  constructor translation-pose-graph-synthetic-receipt
  field
    consistentChainLoopRecovered : Bool
    consistentRMS : String
    inconsistentLoopRMS : String
    disconnectedGraphRejected : Bool
    exactRepositoryCheckoutExecutionPaid : Bool

open TranslationPoseGraphSyntheticReceipt public

currentTranslationPoseGraphSyntheticReceipt : TranslationPoseGraphSyntheticReceipt
currentTranslationPoseGraphSyntheticReceipt =
  translation-pose-graph-synthetic-receipt
    true
    "5.127900497022838e-16 m"
    "1.0 m"
    true
    false

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data TranslationGraphCandidateImpliesFullVIOPermission : Set where

data LowTranslationResidualImpliesCorrectTrajectoryPermission : Set where

data LoopConstraintImpliesLoopIdentityPermission : Set where

translationGraphDoesNotPayFullVIO :
  TranslationGraphCandidateImpliesFullVIOPermission → ⊥
translationGraphDoesNotPayFullVIO ()

lowTranslationResidualDoesNotPayTrajectoryTruth :
  LowTranslationResidualImpliesCorrectTrajectoryPermission → ⊥
lowTranslationResidualDoesNotPayTrajectoryTruth ()

loopConstraintDoesNotAutoPayLoopIdentity :
  LoopConstraintImpliesLoopIdentityPermission → ⊥
loopConstraintDoesNotAutoPayLoopIdentity ()

record TranslationPoseGraphRoadmapStatus : Set where
  constructor translation-pose-graph-roadmap-status
  field
    translationGraphCandidateImplemented : Bool
    loopResidualGateImplemented : Bool
    syntheticTranslationGraphProbePaid : Bool
    rotationGraphOptimizationPaid : Bool
    jointVisualInertialStateOptimizationPaid : Bool
    realPhoneLoopClosureValidated : Bool

open TranslationPoseGraphRoadmapStatus public

currentTranslationPoseGraphRoadmapStatus : TranslationPoseGraphRoadmapStatus
currentTranslationPoseGraphRoadmapStatus =
  translation-pose-graph-roadmap-status true true true false false false
