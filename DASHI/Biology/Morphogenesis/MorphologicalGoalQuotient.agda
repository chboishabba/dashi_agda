module DASHI.Biology.Morphogenesis.MorphologicalGoalQuotient where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Biology.Core.ContextIndexedSystem

-- Morphological targets live in a coarse quotient: many distinct cellular and
-- molecular microstates may realise the same anatomical goal class.
record MorphologicalGoalSystem : Set₁ where
  field
    quotient : QuotientGoal

    Environment : Set
    Perturbation : Set
    LocalAction  : Set
    Defect       : Set

    perturb :
      Perturbation → QuotientGoal.MicroState quotient →
      QuotientGoal.MicroState quotient

    act :
      Environment → LocalAction → QuotientGoal.MicroState quotient →
      QuotientGoal.MicroState quotient

    defect :
      QuotientGoal.GoalClass quotient →
      QuotientGoal.MicroState quotient → Defect

    LowerDefect : Defect → Defect → Set

record MorphologicalGoalWitness
  (M : MorphologicalGoalSystem) : Set₁ where
  open MorphologicalGoalSystem M
  open QuotientGoal quotient
  field
    environment : Environment
    state       : MicroState
    action      : LocalAction

    targetClass : GoalClass
    targetIsSelected : targetClass ≡ target

    targetRealised : classify (coarseGrain state) ≡ targetClass

record MorphologicalCorrectionWitness
  (M : MorphologicalGoalSystem) : Set₁ where
  open MorphologicalGoalSystem M
  open QuotientGoal quotient
  field
    environment  : Environment
    initial      : MicroState
    perturbation : Perturbation
    action       : LocalAction

    correctionDecreasesDefect :
      LowerDefect
        (defect target (act environment action (perturb perturbation initial)))
        (defect target (perturb perturbation initial))

-- Goal language is operational/control-relative.  A target state is not a
-- future event exerting literal retrocausal force on the present.
record MorphologicalGoalAuthorityBoundary : Set₁ where
  field
    goalIsNotFutureCause : Set
    quotientIsNotSemanticRepresentationByDefinition : Set
    anatomicalAttractorIsNotConsciousness : Set
    repairGoalIsNotUniversalTeleology : Set
