module DASHI.Biology.Physical.DynamicTopologyFutureDefectExact where

------------------------------------------------------------------------
-- PNF on a changing biological graph: equal present morphology can hide an
-- interaction edge that changes the result of the same future action.
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

record GraphDevelopmentalState : Set where
  constructor graphDevelopmentalState
  field
    morphology : Bool
    junction : Bool

open GraphDevelopmentalState public

data Action : Set where
  signal : Action

transition : GraphDevelopmentalState → GraphDevelopmentalState
transition (graphDevelopmentalState shape false) =
  graphDevelopmentalState shape false
transition (graphDevelopmentalState shape true) =
  graphDevelopmentalState true true

morphologyProjection : GraphDevelopmentalState → Bool
morphologyProjection = morphology

system : Dependency.DependentActionSystem GraphDevelopmentalState Action
system = record
  { Precondition = λ state action → ⊤
  ; Postcondition = λ before action after → after ≡ transition before
  ; actionLabel = λ action → "signal"
  }

admissible :
  (x : GraphDevelopmentalState) →
  Dependency.AdmissibleAction system x signal
admissible x = record
  { precondition = tt
  ; after = transition x
  ; postcondition = refl
  ; dependencyReceipt = "junction-conditioned developmental signal"
  }

withoutJunction withJunction : GraphDevelopmentalState
withoutJunction = graphDevelopmentalState false false
withJunction = graphDevelopmentalState false true

sameVisibleMorphology :
  morphologyProjection withoutJunction ≡ morphologyProjection withJunction
sameVisibleMorphology = refl

hiddenTopologyDiffers : junction withoutJunction ≢ junction withJunction
hiddenTopologyDiffers = false≢true

leftRun :
  Reachability.Executes system (signal ∷ []) withoutJunction (transition withoutJunction)
leftRun = Reachability.executesCons (admissible withoutJunction) Reachability.executesNil

rightRun :
  Reachability.Executes system (signal ∷ []) withJunction (transition withJunction)
rightRun = Reachability.executesCons (admissible withJunction) Reachability.executesNil

futureMorphologyDiffers :
  morphologyProjection (transition withoutJunction)
  ≢ morphologyProjection (transition withJunction)
futureMorphologyDiffers = false≢true

-- Legacy repository name TerminalisationDefect is used only as the bare
-- future-divergence witness.  No no-reopening theorem is claimed here.
topologyForgettingDynamicDefect :
  Dynamic.TerminalisationDefect system morphologyProjection
topologyForgettingDynamicDefect = record
  { actionTrace = signal ∷ []
  ; left = withoutJunction
  ; right = withJunction
  ; leftAfter = transition withoutJunction
  ; rightAfter = transition withJunction
  ; sameCurrentObservation = refl
  ; leftExecution = leftRun
  ; rightExecution = rightRun
  ; futureObservationsDiffer = futureMorphologyDiffers
  }

morphologyWithoutTopologyIsNotFutureSafe :
  Dynamic.DynamicConsumerSafety system morphologyProjection → ⊥
morphologyWithoutTopologyIsNotFutureSafe safety =
  Dynamic.terminalisationDefectContradictsSafety safety topologyForgettingDynamicDefect

-- Thus the graph itself can belong to the minimal future-sufficient residual.
