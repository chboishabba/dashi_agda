module DASHI.Core.AdaptiveMechanismDiscriminationPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Core.MechanismModelDiscriminationExact as Model

------------------------------------------------------------------------
-- ADAPTIVE MODEL-DISCRIMINATION PLANNER
--
-- Mechanistic explanation is only one possible consumer.  In other domains the
-- consumer may be a repair action, legal classification, monitoring decision,
-- model family, intervention, or provenance judgement.  The sequential planner
-- therefore closes the declared consumer rather than demanding full latent-
-- world identity.
------------------------------------------------------------------------

record AdaptiveDiscriminationProblem : Set₂ where
  constructor adaptiveDiscriminationProblem
  field
    World : Set
    Decision : Set
    Compatible : World → Set
    decide : World → Decision
    worldReference : String
    decisionReference : String

open AdaptiveDiscriminationProblem public

record AdaptiveDiscriminationPlan
    (problem : AdaptiveDiscriminationProblem) : Set₂ where
  constructor adaptiveDiscriminationPlan
  open AdaptiveDiscriminationProblem problem
  field
    plan : Sequential.SequentialConsumerPlan decide Compatible
    planReference : String
    sameObjectPolicyReference : String
    stoppingRuleReference : String

open AdaptiveDiscriminationPlan public

------------------------------------------------------------------------
-- Residual-conditioned next measurement.
------------------------------------------------------------------------

record ResidualConditionedExperimentPolicy
    (problem : AdaptiveDiscriminationProblem) : Set₂ where
  constructor residualConditionedExperimentPolicy
  open AdaptiveDiscriminationProblem problem
  field
    chooseNext : Model.ModelResidual → Synthesis.ExperimentBundle World
    choiceReference : Model.ModelResidual → String
    calibrationReference : Model.ModelResidual → String

open ResidualConditionedExperimentPolicy public

------------------------------------------------------------------------
-- Consumer closure can happen before total mechanism/world identification.
------------------------------------------------------------------------

record DecisionClosureWithoutWorldIdentity
    (problem : AdaptiveDiscriminationProblem) : Set₂ where
  constructor decisionClosureWithoutWorldIdentity
  open AdaptiveDiscriminationProblem problem
  field
    left right : World
    leftCompatible : Compatible left
    rightCompatible : Compatible right
    sameDecision : decide left ≡ decide right
    WorldIdentity : World → World → Set
    worldIdentityNotRequiredReference : String

open DecisionClosureWithoutWorldIdentity public

record AdaptiveMechanismPlannerBoundary : Set where
  constructor adaptiveMechanismPlannerBoundary
  field
    oneFixedExperimentMustBeOptimalForAllResiduals : Bool
    oneFixedExperimentMustBeOptimalForAllResidualsIsFalse :
      oneFixedExperimentMustBeOptimalForAllResiduals ≡ false

    nextExperimentMayDependOnObservedResidual : Bool
    nextExperimentMayDependOnObservedResidualIsTrue :
      nextExperimentMayDependOnObservedResidual ≡ true

    decisionClosureRequiresFullLatentWorldIdentity : Bool
    decisionClosureRequiresFullLatentWorldIdentityIsFalse :
      decisionClosureRequiresFullLatentWorldIdentity ≡ false

    modelDiscriminationCanServeNonMechanisticConsumers : Bool
    modelDiscriminationCanServeNonMechanisticConsumersIsTrue :
      modelDiscriminationCanServeNonMechanisticConsumers ≡ true

    stoppingRuleMustRemainConsumerRelative : Bool
    stoppingRuleMustRemainConsumerRelativeIsTrue :
      stoppingRuleMustRemainConsumerRelative ≡ true

canonicalAdaptiveMechanismPlannerBoundary : AdaptiveMechanismPlannerBoundary
canonicalAdaptiveMechanismPlannerBoundary =
  adaptiveMechanismPlannerBoundary false refl true refl false refl true refl true refl
