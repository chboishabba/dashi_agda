module DASHI.Core.PolicyRelativeProjectionSafety where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- POLICY-RELATIVE PROJECTION SAFETY
--
-- Education / intervention references:
--
--   Alice Brown, Jill Lawrence, Marita Basson, Megan Axelsen,
--   Petrea Redmond, Joanna Turner, Suzanne Maloney, Linda Galligan,
--   "The creation of a nudging protocol to support online student engagement
--   in higher education", Active Learning in Higher Education 24(3),
--   257-271 (2023; first published online 2022).
--   DOI: 10.1177/14697874211039077.
--
--   Melissa Fanshawe, Alice Brown, Petrea Redmond,
--   "Using an online engagement framework to redesign the learning environment
--   for higher education students: A design experiment approach",
--   Online Learning 29(2), 2025.
--   DOI: 10.24059/olj.v29i2.4447.
--
-- These papers motivate the quotient -> intervention loop.  The generic safety
-- theorem below is a DASHI construction and is not attributed to either paper.
------------------------------------------------------------------------

record CoarseInterventionPolicy (Observation Action : Set) : Set where
  constructor coarseInterventionPolicy
  field
    chooseAction : Observation → Action

open CoarseInterventionPolicy public

record PolicyRelativeSafety
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (policy : CoarseInterventionPolicy Observation Action) : Set₁ where
  constructor policyRelativeSafety
  field
    selectedStepCongruence :
      ∀ {left right leftAfter rightAfter action} →
      project left ≡ project right →
      chooseAction policy (project left) ≡ action →
      chooseAction policy (project right) ≡ action →
      Reachability.Executes system (action ∷ []) left leftAfter →
      Reachability.Executes system (action ∷ []) right rightAfter →
      project leftAfter ≡ project rightAfter

open PolicyRelativeSafety public

dynamicSafetyImpliesPolicySafety :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    (policy : CoarseInterventionPolicy Observation Action) →
  Dynamic.DynamicConsumerSafety system project →
  PolicyRelativeSafety system project policy
dynamicSafetyImpliesPolicySafety policy safety =
  policyRelativeSafety
    (λ same leftPolicy rightPolicy leftExecution rightExecution →
      Dynamic.traceCongruence safety same leftExecution rightExecution)

record PolicyExposedQuotientDefect
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (policy : CoarseInterventionPolicy Observation Action) : Set₁ where
  constructor policyExposedQuotientDefect
  field
    left right leftAfter rightAfter : State
    selectedAction : Action
    sameCurrentObservation : project left ≡ project right
    leftPolicySelectsAction :
      chooseAction policy (project left) ≡ selectedAction
    rightPolicySelectsAction :
      chooseAction policy (project right) ≡ selectedAction
    leftExecution :
      Reachability.Executes system (selectedAction ∷ []) left leftAfter
    rightExecution :
      Reachability.Executes system (selectedAction ∷ []) right rightAfter
    selectedFutureObservationsDiffer :
      project leftAfter ≡ project rightAfter → ⊥

open PolicyExposedQuotientDefect public

policyDefectContradictsPolicySafety :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {policy : CoarseInterventionPolicy Observation Action} →
  PolicyRelativeSafety system project policy →
  PolicyExposedQuotientDefect system project policy →
  ⊥
policyDefectContradictsPolicySafety safety defect =
  selectedFutureObservationsDiffer defect
    (selectedStepCongruence safety
      (sameCurrentObservation defect)
      (leftPolicySelectsAction defect)
      (rightPolicySelectsAction defect)
      (leftExecution defect)
      (rightExecution defect))

------------------------------------------------------------------------
-- Full dynamic safety is stronger than safety for one restricted policy.
-- The finite witness below uses a universally safe self-loop policy while an
-- admissible reveal action outside that policy exposes a dynamic defect.
------------------------------------------------------------------------

data DemoState : Set where
  leftNow rightNow leftRevealed rightRevealed : DemoState

data DemoAction : Set where
  hold reveal : DemoAction

data DemoPrecondition : DemoState → DemoAction → Set where
  holdReady : ∀ {state} → DemoPrecondition state hold
  revealLeftReady : DemoPrecondition leftNow reveal
  revealRightReady : DemoPrecondition rightNow reveal

data DemoPostcondition : DemoState → DemoAction → DemoState → Set where
  holdStays : ∀ {state} → DemoPostcondition state hold state
  revealLeft : DemoPostcondition leftNow reveal leftRevealed
  revealRight : DemoPostcondition rightNow reveal rightRevealed

demoActionLabel : DemoAction → String
demoActionLabel hold = "policy-selected hold/self-loop"
demoActionLabel reveal = "non-policy reveal action"

demoSystem : Dependency.DependentActionSystem DemoState DemoAction
demoSystem = record
  { Precondition = DemoPrecondition
  ; Postcondition = DemoPostcondition
  ; actionLabel = demoActionLabel
  }

demoProject : DemoState → Bool
demoProject leftNow = false
demoProject rightNow = false
demoProject leftRevealed = false
demoProject rightRevealed = true

demoPolicy : CoarseInterventionPolicy Bool DemoAction
demoPolicy = coarseInterventionPolicy (λ observation → hold)

holdAdmissible :
  (state : DemoState) →
  Dependency.AdmissibleAction demoSystem state hold
holdAdmissible state = record
  { precondition = holdReady
  ; after = state
  ; postcondition = holdStays
  ; dependencyReceipt = "hold preserves the complete fine state"
  }

holdExecutes :
  (state : DemoState) →
  Reachability.Executes demoSystem (hold ∷ []) state state
holdExecutes state =
  Reachability.executesCons (holdAdmissible state) Reachability.executesNil

demoPolicyIsSafe : PolicyRelativeSafety demoSystem demoProject demoPolicy
demoPolicyIsSafe = policyRelativeSafety proof
  where
    proof :
      ∀ {left right leftAfter rightAfter action} →
      demoProject left ≡ demoProject right →
      chooseAction demoPolicy (demoProject left) ≡ action →
      chooseAction demoPolicy (demoProject right) ≡ action →
      Reachability.Executes demoSystem (action ∷ []) left leftAfter →
      Reachability.Executes demoSystem (action ∷ []) right rightAfter →
      demoProject leftAfter ≡ demoProject rightAfter
    proof same refl refl
      (Reachability.executesCons leftStep Reachability.executesNil)
      (Reachability.executesCons rightStep Reachability.executesNil)
      with Dependency.postcondition leftStep | Dependency.postcondition rightStep
    ... | holdStays | holdStays = same

leftRevealAdmissible :
  Dependency.AdmissibleAction demoSystem leftNow reveal
leftRevealAdmissible = record
  { precondition = revealLeftReady
  ; after = leftRevealed
  ; postcondition = revealLeft
  ; dependencyReceipt = "reveal exposes the left hidden future"
  }

rightRevealAdmissible :
  Dependency.AdmissibleAction demoSystem rightNow reveal
rightRevealAdmissible = record
  { precondition = revealRightReady
  ; after = rightRevealed
  ; postcondition = revealRight
  ; dependencyReceipt = "reveal exposes the right hidden future"
  }

demoDynamicDefect : Dynamic.TerminalisationDefect demoSystem demoProject
demoDynamicDefect =
  Dynamic.terminalisationDefect
    (reveal ∷ [])
    leftNow rightNow leftRevealed rightRevealed
    refl
    (Reachability.executesCons leftRevealAdmissible Reachability.executesNil)
    (Reachability.executesCons rightRevealAdmissible Reachability.executesNil)
    (λ ())

record PolicySafeButNotDynamicallySafeWitness : Set₁ where
  constructor policySafeButNotDynamicallySafeWitness
  field
    policySafety : PolicyRelativeSafety demoSystem demoProject demoPolicy
    unrestrictedDynamicDefect :
      Dynamic.TerminalisationDefect demoSystem demoProject

open PolicySafeButNotDynamicallySafeWitness public

canonicalPolicySafeButNotDynamicallySafeWitness :
  PolicySafeButNotDynamicallySafeWitness
canonicalPolicySafeButNotDynamicallySafeWitness =
  policySafeButNotDynamicallySafeWitness demoPolicyIsSafe demoDynamicDefect
