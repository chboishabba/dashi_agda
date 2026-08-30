module DASHI.Core.AdmissibleTransitionHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- REPO-NATIVE DASHI EXTENSION
--
-- A transition is not merely weighted: it is first proof-relevantly enabled or
-- disabled in the current situated state.  Kinetic/probabilistic weights may be
-- added only on an enabled edge.  This is the shared grammar used by the
-- logistic invariant-region and chemistry adapters.
------------------------------------------------------------------------

record AdmissibleTransitionSystem : Set₁ where
  constructor admissibleTransitionSystem
  field
    State Parameter Move : Set
    Enabled : Move → Parameter → State → Set
    step : Move → Parameter → State → State
    InvariantRegion : State → Set
    preservesInvariant :
      (move : Move) (parameter : Parameter) (state : State) →
      Enabled move parameter state →
      InvariantRegion state →
      InvariantRegion (step move parameter state)
    systemReference : String

open AdmissibleTransitionSystem public

data AdmittedStep
    (system : AdmissibleTransitionSystem)
    (move : Move system)
    (parameter : Parameter system)
    (state : State system) : Set where
  admittedStep :
    Enabled system move parameter state →
    InvariantRegion system state →
    AdmittedStep system move parameter state

admittedStepHasEnablement :
  ∀ {system move parameter state} →
  AdmittedStep system move parameter state →
  Enabled system move parameter state
admittedStepHasEnablement (admittedStep enabled invariant) = enabled

disabledExcludesAdmittedStep :
  ∀ {system move parameter state} →
  (Enabled system move parameter state → ⊥) →
  AdmittedStep system move parameter state → ⊥
disabledExcludesAdmittedStep disabled admitted =
  disabled (admittedStepHasEnablement admitted)

admittedStepPreservesInvariant :
  ∀ {system move parameter state} →
  AdmittedStep system move parameter state →
  InvariantRegion system (step system move parameter state)
admittedStepPreservesInvariant
    {system} {move} {parameter} {state}
    (admittedStep enabled invariant) =
  preservesInvariant system move parameter state enabled invariant

------------------------------------------------------------------------
-- Accessible transition cone and conditional edge weights.
------------------------------------------------------------------------

Accessible :
  (system : AdmissibleTransitionSystem) →
  Parameter system → State system → Move system → Set
Accessible system parameter state move =
  Enabled system move parameter state

record ConditionalEdgeWeight
    (system : AdmissibleTransitionSystem) : Set₁ where
  constructor conditionalEdgeWeight
  field
    Weight : Set
    weight :
      (move : Move system) →
      (parameter : Parameter system) →
      (state : State system) →
      Enabled system move parameter state →
      Weight
    weightReference : String

open ConditionalEdgeWeight public

------------------------------------------------------------------------
-- An intervention can alter the accessible cone by moving the situated state.
-- The theorem does not claim every intervention enables something: an explicit
-- before-disabled / after-enabled witness is required.
------------------------------------------------------------------------

record EnablesMove
    (system : AdmissibleTransitionSystem)
    (intervene : State system → State system)
    (move : Move system)
    (parameter : Parameter system)
    (state : State system) : Set where
  constructor enablesMove
  field
    disabledBefore : Enabled system move parameter state → ⊥
    enabledAfter : Enabled system move parameter (intervene state)
    interventionReference : String

open EnablesMove public

record DisablesMove
    (system : AdmissibleTransitionSystem)
    (intervene : State system → State system)
    (move : Move system)
    (parameter : Parameter system)
    (state : State system) : Set where
  constructor disablesMove
  field
    enabledBefore : Enabled system move parameter state
    disabledAfter : Enabled system move parameter (intervene state) → ⊥
    interventionReference : String

open DisablesMove public

record AdmissibleTransitionBoundary : Set where
  constructor admissibleTransitionBoundary
  field
    disabledTransitionIsMerelyLowProbability : Bool
    disabledTransitionIsMerelyLowProbabilityIsFalse :
      disabledTransitionIsMerelyLowProbability ≡ false

    edgeWeightRequiresEnabledEdge : Bool
    edgeWeightRequiresEnabledEdgeIsTrue :
      edgeWeightRequiresEnabledEdge ≡ true

    admittedStepPreservesDeclaredInvariant : Bool
    admittedStepPreservesDeclaredInvariantIsTrue :
      admittedStepPreservesDeclaredInvariant ≡ true

    interventionMayChangeAccessibleCone : Bool
    interventionMayChangeAccessibleConeIsTrue :
      interventionMayChangeAccessibleCone ≡ true

    everyInterventionChangesAccessibleCone : Bool
    everyInterventionChangesAccessibleConeIsFalse :
      everyInterventionChangesAccessibleCone ≡ false

canonicalAdmissibleTransitionBoundary : AdmissibleTransitionBoundary
canonicalAdmissibleTransitionBoundary =
  admissibleTransitionBoundary false refl true refl true refl true refl false refl
