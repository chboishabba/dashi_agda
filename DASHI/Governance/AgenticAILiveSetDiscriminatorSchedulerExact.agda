module DASHI.Governance.AgenticAILiveSetDiscriminatorSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.TargetIndexedActionNonfactorabilityExact as Target
import DASHI.Core.PathResidualActionRevisionExact as Path
import DASHI.Core.ResidualConditionedExperimentPortfolioExact as Portfolio
import DASHI.Core.ActionFibreClosureStoppingExact as Stop
import DASHI.Governance.AgenticAIResidualRevisionCrossPollinationExact as Agent

------------------------------------------------------------------------
-- AGENTIC AI: LIVE-SET DISCRIMINATOR SCHEDULER
--
-- The next probe depends on which uncertainty remains live: target/goal,
-- world/state, path/history, authority or coalition context.  Highest nominal
-- information gain is filtered by authority before execution.
------------------------------------------------------------------------

data UncertaintyKind : Set where
  targetUncertainty stateUncertainty pathUncertainty authorityUncertainty coalitionUncertainty : UncertaintyKind

data ProbeKind : Set where
  queryGoal inspectState inspectHistory inspectAuthority inspectSharedState holdProbe : ProbeKind

bestProbeFor : UncertaintyKind → ProbeKind
bestProbeFor targetUncertainty = queryGoal
bestProbeFor stateUncertainty = inspectState
bestProbeFor pathUncertainty = inspectHistory
bestProbeFor authorityUncertainty = inspectAuthority
bestProbeFor coalitionUncertainty = inspectSharedState

data NominalMove : Set where measurement perturbation execution : NominalMove

data Admissibility : Set where admitted blocked : Admissibility

record AgenticProbeAssessment : Set where
  constructor agenticProbeAssessment
  field
    uncertainty : UncertaintyKind
    selectedProbe : ProbeKind
    nominalInformationValue : Nat
    admissibility : Admissibility
    liveHypothesisReference : String
    consumerReference : String
    authorityReference : String

open AgenticProbeAssessment public

pathProbe : AgenticProbeAssessment
pathProbe = agenticProbeAssessment pathUncertainty inspectHistory 3 admitted
  "same visible endpoint, different retained path residuals remain live"
  "choose next safe informational action"
  "read-only history inspection admitted"

authorityProbe : AgenticProbeAssessment
authorityProbe = agenticProbeAssessment authorityUncertainty inspectAuthority 2 admitted
  "world state may be sufficiently known while action authority remains unresolved"
  "determine executable rather than merely informative move"
  "authority inspection does not itself expand authority"

record InformationExecutionSplit : Set where
  constructor informationExecutionSplit
  field
    informationallyPreferred : NominalMove
    executableNow : NominalMove
    preferredAuthority : Admissibility
    executableAuthority : Admissibility
    splitReference : String

highInformationButBlocked : InformationExecutionSplit
highInformationButBlocked = informationExecutionSplit
  perturbation measurement blocked admitted
  "perturbation may discriminate more strongly, but absent perturbation authority the scheduler selects an admitted measurement or hold"

record AgenticAILiveSetSchedulerBoundary : Set where
  constructor agenticAILiveSetSchedulerBoundary
  field
    sameObservationFixesBestProbe : Bool
    sameObservationFixesBestProbeIsFalse : sameObservationFixesBestProbe ≡ false
    goalUncertaintyEqualsStateUncertainty : Bool
    goalUncertaintyEqualsStateUncertaintyIsFalse : goalUncertaintyEqualsStateUncertainty ≡ false
    highestInformationGainImpliesExecutable : Bool
    highestInformationGainImpliesExecutableIsFalse : highestInformationGainImpliesExecutable ≡ false
    pathCollisionMayRequireHistoryProbe : Bool
    pathCollisionMayRequireHistoryProbeIsTrue : pathCollisionMayRequireHistoryProbe ≡ true
    actionFibreClosureMayPermitStopping : Bool
    actionFibreClosureMayPermitStoppingIsTrue : actionFibreClosureMayPermitStopping ≡ true

canonicalAgenticAILiveSetSchedulerBoundary : AgenticAILiveSetSchedulerBoundary
canonicalAgenticAILiveSetSchedulerBoundary =
  agenticAILiveSetSchedulerBoundary false refl false refl false refl true refl true refl

existingTargetBoundary : Target.TargetIndexedActionBoundary
existingTargetBoundary = Target.canonicalTargetIndexedActionBoundary

existingPathBoundary : Path.PathResidualActionBoundary
existingPathBoundary = Path.canonicalPathResidualActionBoundary

existingPortfolioBoundary : Portfolio.ResidualConditionedPortfolioBoundary
existingPortfolioBoundary = Portfolio.canonicalResidualConditionedPortfolioBoundary

existingStoppingBoundary : Stop.ActionFibreClosureBoundary
existingStoppingBoundary = Stop.canonicalActionFibreClosureBoundary

existingAgenticBoundary : Agent.AgenticAIResidualRevisionBoundary
existingAgenticBoundary = Agent.canonicalAgenticAIResidualRevisionBoundary
