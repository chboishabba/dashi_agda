module DASHI.Biology.Physical.DevelopmentalHiddenStateFutureDefectExact where

------------------------------------------------------------------------
-- A concrete PNF regression for physical development:
-- equal present morphology does not imply equal developmental future when a
-- hidden regulatory/bioelectric coordinate differs.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

record FineDevelopmentalState : Set where
  constructor fineDevelopmentalState
  field
    morphology : Bool
    hiddenControl : Bool

open FineDevelopmentalState public

data DevelopmentalAction : Set where
  develop : DevelopmentalAction

developmentalTransition : FineDevelopmentalState → FineDevelopmentalState
developmentalTransition (fineDevelopmentalState shape hidden) =
  fineDevelopmentalState (xor shape hidden) hidden

morphologyProjection : FineDevelopmentalState → Bool
morphologyProjection = morphology

developmentalSystem :
  Dependency.DependentActionSystem FineDevelopmentalState DevelopmentalAction
developmentalSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = λ before action after →
      after ≡ developmentalTransition before
  ; actionLabel = λ action → "develop"
  }

admissibleDevelop :
  (x : FineDevelopmentalState) →
  Dependency.AdmissibleAction developmentalSystem x develop
admissibleDevelop x = record
  { precondition = tt
  ; after = developmentalTransition x
  ; postcondition = refl
  ; dependencyReceipt = "deterministic developmental update"
  }

leftState : FineDevelopmentalState
leftState = fineDevelopmentalState false false

rightState : FineDevelopmentalState
rightState = fineDevelopmentalState false true

samePresentMorphology :
  morphologyProjection leftState ≡ morphologyProjection rightState
samePresentMorphology = refl

leftRun :
  Reachability.Executes developmentalSystem
    (develop ∷ []) leftState (developmentalTransition leftState)
leftRun = Reachability.executesCons (admissibleDevelop leftState) Reachability.executesNil

rightRun :
  Reachability.Executes developmentalSystem
    (develop ∷ []) rightState (developmentalTransition rightState)
rightRun = Reachability.executesCons (admissibleDevelop rightState) Reachability.executesNil

futureMorphologiesDiffer :
  morphologyProjection (developmentalTransition leftState)
  ≢ morphologyProjection (developmentalTransition rightState)
futureMorphologiesDiffer = false≢true

morphologyOnlyDynamicDefect :
  Dynamic.TerminalisationDefect developmentalSystem morphologyProjection
morphologyOnlyDynamicDefect = record
  { actionTrace = develop ∷ []
  ; left = leftState
  ; right = rightState
  ; leftAfter = developmentalTransition leftState
  ; rightAfter = developmentalTransition rightState
  ; sameCurrentObservation = refl
  ; leftExecution = leftRun
  ; rightExecution = rightRun
  ; futureObservationsDiffer = futureMorphologiesDiffer
  }

morphologyProjectionCannotBeDynamicallySafe :
  Dynamic.DynamicConsumerSafety developmentalSystem morphologyProjection → ⊥
morphologyProjectionCannotBeDynamicallySafe safety =
  Dynamic.terminalisationDefectContradictsSafety safety morphologyOnlyDynamicDefect
