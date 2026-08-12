module DASHI.Core.AdmissibleReachability where

open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Canonical reflexive/transitive closure of proof-bearing admissible actions.
--
-- TypedDependencyCore already owns the state/action/precondition/postcondition
-- seam.  This module adds only reachability and action-sequence execution.
------------------------------------------------------------------------

data Reachable
    {State Action : Set}
    (system : Dependency.DependentActionSystem State Action)
    : State → State → Set where
  reachableRefl :
    ∀ {state} → Reachable system state state
  reachableStep :
    ∀ {before target}
      (action : Action) →
      (admissible : Dependency.AdmissibleAction system before action) →
      Reachable system (Dependency.after admissible) target →
      Reachable system before target

------------------------------------------------------------------------
-- Same-action-trace execution.  This is the carrier needed for quotient
-- congruence: two projected-equal states are compared under the same sequence
-- of consumer-visible actions, each with its own admissibility witnesses.
------------------------------------------------------------------------

data Executes
    {State Action : Set}
    (system : Dependency.DependentActionSystem State Action)
    : List Action → State → State → Set where
  executesNil :
    ∀ {state} → Executes system [] state state
  executesCons :
    ∀ {before target action actions}
      (admissible : Dependency.AdmissibleAction system before action) →
      Executes system actions (Dependency.after admissible) target →
      Executes system (action ∷ actions) before target

executesImpliesReachable :
  ∀ {State Action}
    {system : Dependency.DependentActionSystem State Action}
    {actions before after} →
  Executes system actions before after →
  Reachable system before after
executesImpliesReachable executesNil = reachableRefl
executesImpliesReachable (executesCons {action = action} admissible rest) =
  reachableStep action admissible (executesImpliesReachable rest)

record CorrectiveReachability
    {State Action : Set}
    (system : Dependency.DependentActionSystem State Action)
    (suppressed live : State) : Set where
  constructor correctiveReachability
  field
    reopeningPath : Reachable system suppressed live

open CorrectiveReachability public
