module DASHI.Biology.AgenticLevinWolframResidualCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AgenticMaterialsControlCore as Agentic
import DASHI.Biology.Levin.LevinBioelectricAgencyCore as Levin
import DASHI.Biology.Levin.HierarchicalGoalMemory as Goal
import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Core.ResidualActionSalienceExact as Salience
import DASHI.Core.TargetIndexedActionNonfactorabilityExact as TargetAction
import DASHI.Core.PathResidualActionRevisionExact as PathAction

------------------------------------------------------------------------
-- AGENTIC / LEVIN / WOLFRAM CROSS-POLLINATION
--
-- The shared theorem shape is not that these theories are identical.  It is
-- that an endpoint-only observer can erase distinctions that remain relevant to
-- a target-directed adaptive system: latent target, path history, retained
-- evidence, consumer and authority may all change what should happen next.
------------------------------------------------------------------------

agenticBoundary : Agentic.AgenticMaterial → Agentic.OpenSystemBookkeeping
agenticBoundary M = Agentic.thermodynamics M

levinBoundary : Levin.LevinBioelectricAgencyCore
levinBoundary = Levin.canonicalLevinBioelectricAgencyCore

hierarchicalGoalBoundary : Goal.HierarchicalGoalBoundary
hierarchicalGoalBoundary = Goal.canonicalHierarchicalGoalBoundary

targetIndexedBoundary : TargetAction.TargetIndexedActionBoundary
targetIndexedBoundary = TargetAction.canonicalTargetIndexedActionBoundary

pathResidualBoundary : PathAction.PathResidualActionBoundary
pathResidualBoundary = PathAction.canonicalPathResidualActionBoundary

revisionBoundary : Revision.AppendOnlyEvidenceResidualRevisionBoundary
revisionBoundary = Revision.canonicalAppendOnlyEvidenceResidualRevisionBoundary

salienceBoundary : Salience.ResidualActionSalienceBoundary
salienceBoundary = Salience.canonicalResidualActionSalienceBoundary

------------------------------------------------------------------------
-- Exact Wolfram-style fixture already owned by NaturalSystemsHyperfabricExact:
-- both rewrite orders expose visible endpoint 3 but retain path residues 1/2.
------------------------------------------------------------------------

data ResidualNextAction : Set where inspectHistory holdHistory : ResidualNextAction

nextFromPathResidual : Nat → ResidualNextAction
nextFromPathResidual zero = holdHistory
nextFromPathResidual (suc zero) = inspectHistory
nextFromPathResidual (suc (suc n)) = holdHistory

naturalVisibleEndpointCollision :
  Natural.visibleEndpoint (Natural.executeMultiway Natural.leftThenRight)
  ≡ Natural.visibleEndpoint (Natural.executeMultiway Natural.rightThenLeft)
naturalVisibleEndpointCollision = Natural.multiwayPathsShareVisibleEndpoint

naturalPathResidualLeft :
  Natural.pathResidual (Natural.executeMultiway Natural.leftThenRight) ≡ 1
naturalPathResidualLeft = refl

naturalPathResidualRight :
  Natural.pathResidual (Natural.executeMultiway Natural.rightThenLeft) ≡ 2
naturalPathResidualRight = refl

naturalNextActionsDiffer :
  nextFromPathResidual
    (Natural.pathResidual (Natural.executeMultiway Natural.leftThenRight))
  ≡
  nextFromPathResidual
    (Natural.pathResidual (Natural.executeMultiway Natural.rightThenLeft))
  → ⊥
naturalNextActionsDiffer ()

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record AgenticLevinWolframCrossPollinationBoundary : Set where
  constructor agenticLevinWolframCrossPollinationBoundary
  field
    sameEndpointImpliesSameAgentState : Bool
    sameEndpointImpliesSameAgentStateIsFalse :
      sameEndpointImpliesSameAgentState ≡ false

    sameEndpointImpliesSameNextAction : Bool
    sameEndpointImpliesSameNextActionIsFalse :
      sameEndpointImpliesSameNextAction ≡ false

    correctiveBehaviourRequiresStaticUnrewritableGoal : Bool
    correctiveBehaviourRequiresStaticUnrewritableGoalIsFalse :
      correctiveBehaviourRequiresStaticUnrewritableGoal ≡ false

    persistentGoalRewriteErasesPriorHistory : Bool
    persistentGoalRewriteErasesPriorHistoryIsFalse :
      persistentGoalRewriteErasesPriorHistory ≡ false

    hierarchicalGoalControlImpliesHumanLikeMetacognition : Bool
    hierarchicalGoalControlImpliesHumanLikeMetacognitionIsFalse :
      hierarchicalGoalControlImpliesHumanLikeMetacognition ≡ false

    pathResidualCanRemainActionRelevantAfterEndpointMerge : Bool
    pathResidualCanRemainActionRelevantAfterEndpointMergeIsTrue :
      pathResidualCanRemainActionRelevantAfterEndpointMerge ≡ true

    appendOnlyHistoryCanSupportGoalOrActionRevision : Bool
    appendOnlyHistoryCanSupportGoalOrActionRevisionIsTrue :
      appendOnlyHistoryCanSupportGoalOrActionRevision ≡ true

    actionRevisionCreatesExecutionAuthority : Bool
    actionRevisionCreatesExecutionAuthorityIsFalse :
      actionRevisionCreatesExecutionAuthority ≡ false

    reading : String

canonicalAgenticLevinWolframCrossPollinationBoundary :
  AgenticLevinWolframCrossPollinationBoundary
canonicalAgenticLevinWolframCrossPollinationBoundary =
  agenticLevinWolframCrossPollinationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    "Endpoint, target, path residue, retained evidence, consumer salience and execution authority are distinct coordinates. Levin-style hierarchical goal restoration/rewrite and Wolfram-style multiway endpoint merging therefore cross-pollinate with the residual-action architecture without being identified with one another."
