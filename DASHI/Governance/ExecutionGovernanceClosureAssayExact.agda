module DASHI.Governance.ExecutionGovernanceClosureAssayExact where

------------------------------------------------------------------------
-- EXECUTION GOVERNANCE CLOSURE ASSAYS
--
-- Completes the hard-gate side of the physical-agent tranche:
--   * coverage/externality residuals;
--   * jointly unsatisfiable obligations;
--   * evaluator/reward-channel independence;
--   * purpose-indexed data storage/join/inference/action separation;
--   * local-step safety != trajectory safety.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Safety-language coverage and unresolved externality.
------------------------------------------------------------------------

data ConsequenceClass : Set where
  reversibleLowConsequence irreversibleHighConsequence : ConsequenceClass

data CoverageState : Set where
  completeCoverage unresolvedExternality : CoverageState

data AutonomousExecution : ConsequenceClass → CoverageState → Set where
  lowConsequenceExecution : AutonomousExecution reversibleLowConsequence completeCoverage
  lowConsequenceWithResidual : AutonomousExecution reversibleLowConsequence unresolvedExternality
  highConsequenceCovered : AutonomousExecution irreversibleHighConsequence completeCoverage

unresolvedHighConsequenceBlocksAutonomousExecution :
  AutonomousExecution irreversibleHighConsequence unresolvedExternality → ⊥
unresolvedHighConsequenceBlocksAutonomousExecution ()

------------------------------------------------------------------------
-- 2. Jointly unsatisfiable obligations produce halt/escalate, not workaround.
------------------------------------------------------------------------

data ObligationState : Set where
  jointlySatisfiable jointlyUnsatisfiable : ObligationState

data GovernanceResponse : Set where
  executeOrdinary halt escalate requestResolution : GovernanceResponse

responseToObligations : ObligationState → GovernanceResponse
responseToObligations jointlySatisfiable = executeOrdinary
responseToObligations jointlyUnsatisfiable = requestResolution

unsatDoesNotYieldOrdinaryExecution :
  responseToObligations jointlyUnsatisfiable ≡ executeOrdinary → ⊥
unsatDoesNotYieldOrdinaryExecution ()

------------------------------------------------------------------------
-- 3. Evaluator tampering does not become independent success evidence.
------------------------------------------------------------------------

data EvaluatorState : Set where
  evaluatorIndependent evaluatorAgentInfluenced : EvaluatorState

data SuccessEvidence : EvaluatorState → Set where
  independentSuccess : SuccessEvidence evaluatorIndependent

agentInfluencedEvaluatorCannotIssueIndependentSuccess :
  SuccessEvidence evaluatorAgentInfluenced → ⊥
agentInfluencedEvaluatorCannotIssueIndependentSuccess ()

------------------------------------------------------------------------
-- 4. Storage, joining, inference and action are separate permissions.
------------------------------------------------------------------------

data DataItem : Set where datumA datumB derivedDatum : DataItem
data Purpose : Set where researchPurpose enforcementPurpose : Purpose

data MayStore : DataItem → Purpose → Set where
  storeAForResearch : MayStore datumA researchPurpose
  storeBForResearch : MayStore datumB researchPurpose

data MayJoin : DataItem → DataItem → Purpose → Set where
  joinForResearch : MayJoin datumA datumB researchPurpose

data MayInfer : DataItem → Purpose → Set where
  inferForResearch : MayInfer derivedDatum researchPurpose

data MayActOn : DataItem → Purpose → Set where
  actOnForResearch : MayActOn derivedDatum researchPurpose

storeDoesNotManufactureEnforcementJoin :
  MayJoin datumA datumB enforcementPurpose → ⊥
storeDoesNotManufactureEnforcementJoin ()

researchInferenceDoesNotManufactureEnforcementAction :
  MayActOn derivedDatum enforcementPurpose → ⊥
researchInferenceDoesNotManufactureEnforcementAction ()

------------------------------------------------------------------------
-- 5. Local acceptability need not imply trajectory acceptability.
------------------------------------------------------------------------

data LocalStep : Set where step1 step2 step3 : LocalStep

data LocallyAcceptable : LocalStep → Set where
  step1Okay : LocallyAcceptable step1
  step2Okay : LocallyAcceptable step2
  step3Okay : LocallyAcceptable step3

data TrajectoryClass : Set where safeTrajectory pathologicalAttractor : TrajectoryClass

threeStepTrajectory : LocalStep → LocalStep → LocalStep → TrajectoryClass
threeStepTrajectory step1 step2 step3 = pathologicalAttractor
threeStepTrajectory _ _ _ = safeTrajectory

allThreeStepsLocallyAcceptable :
  LocallyAcceptable step1 × LocallyAcceptable step2 × LocallyAcceptable step3
allThreeStepsLocallyAcceptable = step1Okay , (step2Okay , step3Okay)

locallyAcceptableSequenceCanStillBePathological :
  threeStepTrajectory step1 step2 step3 ≡ pathologicalAttractor
locallyAcceptableSequenceCanStillBePathological = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ExecutionGovernanceClosureBoundary : Set where
  constructor execution-governance-closure-boundary
  field
    declaredInvariantAutomaticallyCoversAllAffectedCoordinates : Bool
    declaredInvariantAutomaticallyCoversAllAffectedCoordinatesIsFalse :
      declaredInvariantAutomaticallyCoversAllAffectedCoordinates ≡ false
    unresolvedExternalityPermitsIrreversibleAutonomy : Bool
    unresolvedExternalityPermitsIrreversibleAutonomyIsFalse :
      unresolvedExternalityPermitsIrreversibleAutonomy ≡ false
    unsatisfiableObligationsAreOptimizerChallenge : Bool
    unsatisfiableObligationsAreOptimizerChallengeIsFalse :
      unsatisfiableObligationsAreOptimizerChallenge ≡ false
    agentInfluencedEvaluatorIsIndependentEvidence : Bool
    agentInfluencedEvaluatorIsIndependentEvidenceIsFalse :
      agentInfluencedEvaluatorIsIndependentEvidence ≡ false
    mayStoreImpliesMayJoinInferAndAct : Bool
    mayStoreImpliesMayJoinInferAndActIsFalse : mayStoreImpliesMayJoinInferAndAct ≡ false
    everyLocallyAcceptableSequenceIsSafeTrajectory : Bool
    everyLocallyAcceptableSequenceIsSafeTrajectoryIsFalse :
      everyLocallyAcceptableSequenceIsSafeTrajectory ≡ false
    reading : String

canonicalExecutionGovernanceClosureBoundary : ExecutionGovernanceClosureBoundary
canonicalExecutionGovernanceClosureBoundary =
  execution-governance-closure-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Execution closure requires more than a locally valid safety predicate: high-consequence actions block on unresolved externality; jointly unsatisfiable obligations route to governance resolution; agent-influenced evaluators cannot certify independent success; storage/join/inference/action permissions remain distinct; and locally acceptable steps can compose into a pathological trajectory."
