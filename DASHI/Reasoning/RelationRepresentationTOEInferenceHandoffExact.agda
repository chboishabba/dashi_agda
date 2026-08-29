module DASHI.Reasoning.RelationRepresentationTOEInferenceHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationRepresentationStudyValidationObligationsExact as Study

------------------------------------------------------------------------
-- RELATION-REPRESENTATION -> TOE STAGE-6/7 INFERENCE HANDOFF
--
-- This module is deliberately a handoff contract, not a second inference
-- calculus.  The intended downstream owners are the Stage-6/7 modules currently
-- developed on draft PR #636:
--
--   DASHI.Core.PredictionEnvelopeExact
--   DASHI.Core.CalibratedExperimentInferenceExact
--   DASHI.Core.RobustExperimentInferenceFrontierExact
--
-- Until those owners merge into the common base, this branch does not import or
-- duplicate them.  The purpose here is to state which study/producer artifacts
-- should populate which inferential stage once the owner modules are available.
------------------------------------------------------------------------

data InferenceStage : Set where
  evidenceFibreStage
  predictionEnvelopeStage
  calibratedInferenceStage
  certifiedSensitivityStage
  robustnessDiscrepancyStage
  heldOutValidationStage
  experimentDiscriminationStage
  : InferenceStage

record ArtifactHandoff : Set where
  constructor artifactHandoff
  field
    artifact : Study.ValidationArtifact
    destination : InferenceStage
    handoffReading : String

open ArtifactHandoff public

modelIdentityHandoff : ArtifactHandoff
modelIdentityHandoff =
  artifactHandoff Study.exactModelIdentity evidenceFibreStage
    "Exact model identity belongs in the evidence fibre/provenance of the experiment; it is not itself a prediction or posterior."

modelRevisionHandoff : ArtifactHandoff
modelRevisionHandoff =
  artifactHandoff Study.modelRevisionOrWeightHash evidenceFibreStage
    "A pinned revision/weight hash is evidence provenance needed before cross-model or checkpoint claims can be compared."

rawPairHandoff : ArtifactHandoff
rawPairHandoff =
  artifactHandoff Study.rawPairedExamples evidenceFibreStage
    "Raw matched pairs define part of the compatible-state/evidence surface from which a prediction envelope may later be formed."

rawActivationHandoff : ArtifactHandoff
rawActivationHandoff =
  artifactHandoff Study.rawEmbeddingsOrActivations evidenceFibreStage
    "Raw embeddings/activations are producer evidence.  Their existence does not yet imply point-identifiability, probability, or realization."

rawScoreHandoff : ArtifactHandoff
rawScoreHandoff =
  artifactHandoff Study.rawPredictionOrSimilarityScores predictionEnvelopeStage
    "Raw prediction/similarity scores can populate a declared prediction consumer, but do not by themselves specify posterior or confidence semantics."

humanJudgmentHandoff : ArtifactHandoff
humanJudgmentHandoff =
  artifactHandoff Study.groundTruthOrHumanJudgments calibratedInferenceStage
    "Human/ground-truth labels may support calibration or scoring procedures only after their statistical semantics and split are declared."

statisticalReceiptHandoff : ArtifactHandoff
statisticalReceiptHandoff =
  artifactHandoff Study.statisticalTestReceipt calibratedInferenceStage
    "A statistical-test receipt belongs in calibrated/weighted inference and must remain distinct from deterministic admissibility."

checkpointHandoff : ArtifactHandoff
checkpointHandoff =
  artifactHandoff Study.checkpointSeries heldOutValidationStage
    "A checkpoint series supports temporal/future validation; one successful checkpoint does not establish future safety."

interventionTrajectoryHandoff : ArtifactHandoff
interventionTrajectoryHandoff =
  artifactHandoff Study.interventionTrajectory certifiedSensitivityStage
    "An intervention trajectory may support a trajectory-sensitivity claim only when paired with the required variational/derivative receipt."

manifoldHandoff : ArtifactHandoff
manifoldHandoff =
  artifactHandoff Study.fittedGeometryOrManifold robustnessDiscrepancyStage
    "A fitted manifold is a model component whose discrepancy and adequacy must be tested; fit does not identify the manifold with semantic ontology."

heldOutSplitHandoff : ArtifactHandoff
heldOutSplitHandoff =
  artifactHandoff Study.trainValidationTestSplit heldOutValidationStage
    "Held-out partition provenance is required before repair/generalization support can be distinguished from training fit."

allCanonicalHandoffs : List ArtifactHandoff
allCanonicalHandoffs =
  modelIdentityHandoff
  ∷ modelRevisionHandoff
  ∷ rawPairHandoff
  ∷ rawActivationHandoff
  ∷ rawScoreHandoff
  ∷ humanJudgmentHandoff
  ∷ statisticalReceiptHandoff
  ∷ checkpointHandoff
  ∷ interventionTrajectoryHandoff
  ∷ manifoldHandoff
  ∷ heldOutSplitHandoff
  ∷ []

------------------------------------------------------------------------
-- The post-merge bridge should be thin: once the Stage-6/7 owners are on the
-- shared base, this handoff is replaced/extended by imports and theorem-level
-- adapters, not by copying their definitions into Reasoning.
------------------------------------------------------------------------

record TOEInferenceHandoffBoundary : Set where
  constructor toeInferenceHandoffBoundary
  field
    rawScoresArePosteriorByDefault : Bool
    rawScoresArePosteriorByDefaultIsFalse :
      rawScoresArePosteriorByDefault ≡ false

    fittedOperatorIsPointIdentifiableByDefault : Bool
    fittedOperatorIsPointIdentifiableByDefaultIsFalse :
      fittedOperatorIsPointIdentifiableByDefault ≡ false

    declaredFiniteDifferenceIsCertifiedJacobian : Bool
    declaredFiniteDifferenceIsCertifiedJacobianIsFalse :
      declaredFiniteDifferenceIsCertifiedJacobian ≡ false

    goodFitEstablishesModelAdequacy : Bool
    goodFitEstablishesModelAdequacyIsFalse :
      goodFitEstablishesModelAdequacy ≡ false

    trainingFitEstablishesHeldOutSupport : Bool
    trainingFitEstablishesHeldOutSupportIsFalse :
      trainingFitEstablishesHeldOutSupport ≡ false

    stage67OwnersShouldBeReusedAfterMerge : Bool
    stage67OwnersShouldBeReusedAfterMergeIsTrue :
      stage67OwnersShouldBeReusedAfterMerge ≡ true

canonicalTOEInferenceHandoffBoundary : TOEInferenceHandoffBoundary
canonicalTOEInferenceHandoffBoundary =
  toeInferenceHandoffBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
