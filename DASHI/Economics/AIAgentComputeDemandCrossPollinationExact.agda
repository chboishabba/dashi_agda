module DASHI.Economics.AIAgentComputeDemandCrossPollinationExact where

open import DASHI.Core.Prelude
import DASHI.Economics.ComputeScalingUnitEconomicsExact as Scaling
import DASHI.Economics.UnitEconomicsMarginExact as Unit
import DASHI.Governance.MHSButterBenchPhysicalAgentCrossPollinationExact as AgentGov

------------------------------------------------------------------------
-- AGENTIC WORKLOAD / COMPUTE-DEMAND CROSS-POLLINATION
--
-- Reuses the existing governance seam where request, execution and physical
-- effect are not collapsed.  Here, prompt/request volume, generated tokens,
-- agent steps, useful task completion and economic value are likewise distinct.
------------------------------------------------------------------------

record AgenticComputeSurface : Set₁ where
  field
    scalingSystem : Scaling.ComputeScalingSystem
    unitSystem : Unit.UnitEconomicsSystem
    Agent Task : Set
    AgentStep ToolCall CompletedTask EconomicValue : Agent → Task → Set
    requestTokens outputTokens hiddenReasoningTokens : Agent → Task → Set

open AgenticComputeSurface public

record AgenticWorkloadExpansion
    (surface : AgenticComputeSurface)
    (agent : Agent surface)
    (task : Task surface) : Set₁ where
  field
    agentStep : AgentStep surface agent task
    toolCall : ToolCall surface agent task
    workloadExpanded : Set

record AgenticUsefulCompletion
    (surface : AgenticComputeSurface)
    (agent : Agent surface)
    (task : Task surface) : Set₁ where
  field
    completedTask : CompletedTask surface agent task
    completionReceipt : Set

record AgenticEconomicValueReceipt
    (surface : AgenticComputeSurface)
    (agent : Agent surface)
    (task : Task surface) : Set₁ where
  field
    usefulCompletion : AgenticUsefulCompletion surface agent task
    economicValue : EconomicValue surface agent task
    valueProducer : Set

data MoreAgentStepsImpliesMoreEconomicValuePermission : Set where

data MoreTokensImpliesMoreUsefulWorkPermission : Set where

data ToolCallAcceptedImpliesTaskCompletedPermission : Set where

data LowerCostPerTokenImpliesLowerCostPerCompletedTaskPermission : Set where

moreAgentStepsDoesNotAutoPromoteToMoreEconomicValue :
  MoreAgentStepsImpliesMoreEconomicValuePermission → ⊥
moreAgentStepsDoesNotAutoPromoteToMoreEconomicValue ()

moreTokensDoesNotAutoPromoteToMoreUsefulWork :
  MoreTokensImpliesMoreUsefulWorkPermission → ⊥
moreTokensDoesNotAutoPromoteToMoreUsefulWork ()

toolCallAcceptedDoesNotAutoPromoteToTaskCompleted :
  ToolCallAcceptedImpliesTaskCompletedPermission → ⊥
toolCallAcceptedDoesNotAutoPromoteToTaskCompleted ()

lowerCostPerTokenDoesNotAutoPromoteToLowerCostPerCompletedTask :
  LowerCostPerTokenImpliesLowerCostPerCompletedTaskPermission → ⊥
lowerCostPerTokenDoesNotAutoPromoteToLowerCostPerCompletedTask ()

-- Existing AI/governance source-bounded cross-pollination remains the
-- authority for request/execution/effect non-collapse.
existingAgentGovernanceBoundary :
  AgentGov.MHSButterBenchPhysicalAgentCrossPollination
existingAgentGovernanceBoundary =
  AgentGov.canonicalMHSButterBenchPhysicalAgentCrossPollination
