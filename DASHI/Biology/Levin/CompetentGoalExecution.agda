module DASHI.Biology.Levin.CompetentGoalExecution where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; _⊔_; lsuc)

------------------------------------------------------------------------
-- High-level goal commands and competent lower-level execution.
--
-- A command supplies a target while the material system selects a policy.
-- This separates instruction from micromanaged construction and leaves
-- persuasion/acceptance explicit rather than assuming automatic obedience.

record GoalExecutionSystem
  {ℓs ℓg ℓc ℓp : Level} : Set (lsuc (ℓs ⊔ ℓg ⊔ ℓc ⊔ ℓp)) where
  field
    State   : Set ℓs
    Goal    : Set ℓg
    Command : Set ℓc
    Policy  : Set ℓp

    interpret : Command → Goal
    accept    : State → Command → Bool
    discover  : State → Goal → Policy
    execute   : Policy → State → State
    satisfies : State → Goal → Bool
    samePolicy : Policy → Policy → Bool

open GoalExecutionSystem public

record CompetentExecutionWitness
  {ℓs ℓg ℓc ℓp : Level}
  (S : GoalExecutionSystem {ℓs} {ℓg} {ℓc} {ℓp}) :
  Set (ℓs ⊔ ℓc) where
  field
    initial : State S
    command : Command S
    commandAccepted : accept S initial command ≡ true
    reachesCommandedGoal :
      satisfies S
        (execute S (discover S initial (interpret S command)) initial)
        (interpret S command)
      ≡ true

open CompetentExecutionWitness public

record GoalUnderdeterminesTrajectoryWitness
  {ℓs ℓg ℓc ℓp : Level}
  (S : GoalExecutionSystem {ℓs} {ℓg} {ℓc} {ℓp}) :
  Set (ℓs ⊔ ℓc ⊔ ℓp) where
  field
    initial : State S
    command : Command S
    policy₁ policy₂ : Policy S
    distinctPolicies : samePolicy S policy₁ policy₂ ≡ false
    policy₁Succeeds :
      satisfies S (execute S policy₁ initial) (interpret S command) ≡ true
    policy₂Succeeds :
      satisfies S (execute S policy₂ initial) (interpret S command) ≡ true

open GoalUnderdeterminesTrajectoryWitness public

data ControlMode : Set where
  forcedConstruction : ControlMode
  goalInstruction    : ControlMode
  negotiatedPersuasion : ControlMode

canonicalCompetentExecutionNotes : List String
canonicalCompetentExecutionNotes =
  "A high-level goal command does not definitionally specify the microtrajectory"
  ∷ "Competence requires an explicit success witness under a selected policy"
  ∷ "Acceptance is represented separately so instruction is not confused with coercion"
  ∷ "Goal-directed execution does not by itself establish consciousness or linguistic understanding"
  ∷ []

record CompetentExecutionBoundary : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    commandIsNotMicrotrajectory : Bool
    commandIsNotMicrotrajectoryIsFalse : commandIsNotMicrotrajectory ≡ false

    competenceIsNotConsciousness : Bool
    competenceIsNotConsciousnessIsFalse : competenceIsNotConsciousness ≡ false

open CompetentExecutionBoundary public

canonicalCompetentExecutionBoundary : CompetentExecutionBoundary
canonicalCompetentExecutionBoundary = record
  { candidateOnly = true
  ; candidateOnlyIsTrue = refl
  ; commandIsNotMicrotrajectory = false
  ; commandIsNotMicrotrajectoryIsFalse = refl
  ; competenceIsNotConsciousness = false
  ; competenceIsNotConsciousnessIsFalse = refl
  }
