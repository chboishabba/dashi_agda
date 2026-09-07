module DASHI.Governance.AgenticAIResidualRevisionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Core.ResidualActionSalienceExact as Salience
import DASHI.Core.TargetIndexedActionNonfactorabilityExact as TargetAction
import DASHI.Core.PathResidualActionRevisionExact as PathAction
import DASHI.Core.ProofCarryingPhysicalExecutionBoundaryExact as Physical
import DASHI.Governance.MHSButterBenchPhysicalAgentCrossPollinationExact as MHS

data AgentEvidenceStage : Set where
  initialObservation toolResult resourceTelemetry sharedStateObservation postActionObservation governanceUpdate : AgentEvidenceStage


record AgenticAIDecisionContext : Set where
  constructor agenticAIDecisionContext
  field
    goalReference : String
    observationReference : String
    pathHistoryReference : String
    liveHypothesisReference : String
    authorityReference : String
    retainedEvidenceReference : String

open AgenticAIDecisionContext public

mhsBoundary : MHS.MHSButterBenchPhysicalAgentCrossPollination
mhsBoundary = MHS.canonicalMHSButterBenchPhysicalAgentCrossPollination

physicalBoundary : Physical.ProofCarryingPhysicalExecutionBoundary
physicalBoundary = Physical.canonicalProofCarryingPhysicalExecutionBoundary

revisionBoundary : Revision.AppendOnlyEvidenceResidualRevisionBoundary
revisionBoundary = Revision.canonicalAppendOnlyEvidenceResidualRevisionBoundary

salienceBoundary : Salience.ResidualActionSalienceBoundary
salienceBoundary = Salience.canonicalResidualActionSalienceBoundary

targetActionBoundary : TargetAction.TargetIndexedActionBoundary
targetActionBoundary = TargetAction.canonicalTargetIndexedActionBoundary

pathActionBoundary : PathAction.PathResidualActionBoundary
pathActionBoundary = PathAction.canonicalPathResidualActionBoundary

agentTargetNonfactorabilityWitness : TargetAction.SameObservationDifferentTargetAction TargetAction.toyPolicy
agentTargetNonfactorabilityWitness = TargetAction.sameSignalDifferentGoalAction

agentPathNonfactorabilityWitness : PathAction.SameEndpointDifferentResidualAction PathAction.toySystem
agentPathNonfactorabilityWitness = PathAction.sameEndpointDifferentPathAction

record AgenticAIResidualRevisionBoundary : Set where
  constructor agenticAIResidualRevisionBoundary
  field
    sameLatestObservationForcesSameAction : Bool
    sameLatestObservationForcesSameActionIsFalse : sameLatestObservationForcesSameAction ≡ false
    sameVisibleEndpointForcesSameActionHistory : Bool
    sameVisibleEndpointForcesSameActionHistoryIsFalse : sameVisibleEndpointForcesSameActionHistory ≡ false
    appendOnlyAgentMemoryForcesMonotonePolicy : Bool
    appendOnlyAgentMemoryForcesMonotonePolicyIsFalse : appendOnlyAgentMemoryForcesMonotonePolicy ≡ false
    goalRevisionRequiresDeletingPriorEvidence : Bool
    goalRevisionRequiresDeletingPriorEvidenceIsFalse : goalRevisionRequiresDeletingPriorEvidence ≡ false
    resourcePressureCreatesPermission : Bool
    resourcePressureCreatesPermissionIsFalse : resourcePressureCreatesPermission ≡ false
    sharedStateAgreementCreatesCoalitionAuthority : Bool
    sharedStateAgreementCreatesCoalitionAuthorityIsFalse : sharedStateAgreementCreatesCoalitionAuthority ≡ false
    actionSalienceMayChangeWithGoalOrConsumer : Bool
    actionSalienceMayChangeWithGoalOrConsumerIsTrue : actionSalienceMayChangeWithGoalOrConsumer ≡ true
    revisedActionStillNeedsExecutionAdmission : Bool
    revisedActionStillNeedsExecutionAdmissionIsTrue : revisedActionStillNeedsExecutionAdmission ≡ true
    reading : String

canonicalAgenticAIResidualRevisionBoundary : AgenticAIResidualRevisionBoundary
canonicalAgenticAIResidualRevisionBoundary =
  agenticAIResidualRevisionBoundary
    false refl false refl false refl false refl false refl false refl true refl true refl
    "Agentic AI planning is target-, history-, hypothesis-, consumer- and authority-indexed. Append-only tool/telemetry evidence may revise rather than monotonically strengthen a policy, while MHS/Butter-Bench execution and resource-pressure boundaries block recommendation or urgency from becoming permission."
