module DASHI.Biology.Levin.ColonyCollectiveDecisionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Biology.Levin.ComponentCausalRoleBoundary as Causal

record ColonyDecisionProtocol : Set where
  field
    localInteractionRuleMeasured : Bool
    candidateOptionsSpecified : Bool
    recruitmentOrInhibitionMeasured : Bool
    quorumOrThresholdMeasured : Bool
    individualTurnoverMeasured : Bool
    collectiveDecisionMeasured : Bool
    leaderRemovalOrAbsenceTested : Bool
    perturbationOfCommunicationAttempted : Bool
    robustnessAcrossGroupSizeMeasured : Bool

record ColonyCollectiveDecisionBoundary : Set where
  field
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    causalRoleBoundary : Causal.ComponentCausalRoleBoundary
    collectiveDecisionWithoutCentralControllerAdmissible : Bool
    localRuleNotWholeColonyGoalByDefinition : Bool
    quorumNotConsensusByDefinition : Bool
    robustDecisionNotCollectiveConsciousness : Bool
    individualReplaceabilityNotIndividualIrrelevance : Bool
    colonyAgencyRequiresScaleSpecificGoalWitness : Bool
    interpretation : String

canonicalColonyCollectiveDecisionBoundary : ColonyCollectiveDecisionBoundary
canonicalColonyCollectiveDecisionBoundary = record
  { problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; causalRoleBoundary = Causal.canonicalComponentCausalRoleBoundary
  ; collectiveDecisionWithoutCentralControllerAdmissible = true
  ; localRuleNotWholeColonyGoalByDefinition = true
  ; quorumNotConsensusByDefinition = true
  ; robustDecisionNotCollectiveConsciousness = true
  ; individualReplaceabilityNotIndividualIrrelevance = true
  ; colonyAgencyRequiresScaleSpecificGoalWitness = true
  ; interpretation = "Social colonies may select among alternatives through distributed recruitment, inhibition and quorum dynamics without a central controller; the collective decision, individual causal roles and any colony-level goal remain distinct scale-indexed claims"
  }
