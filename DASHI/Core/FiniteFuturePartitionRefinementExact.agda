module DASHI.Core.FiniteFuturePartitionRefinementExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- FINITE FUTURE-SIGNATURE PARTITION REFINEMENT
------------------------------------------------------------------------

DepthEquivalent :
  ∀ {State Action Observation : Set} →
  Nat →
  (State → Observation) →
  (Action → State → State) →
  State → State → Set
DepthEquivalent {Action = Action} zero observe step left right =
  observe left ≡ observe right
DepthEquivalent {Action = Action} (suc depth) observe step left right =
  (observe left ≡ observe right)
  × ((action : Action) →
      DepthEquivalent depth observe step
        (step action left) (step action right))

depthEquivalentMonotone :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {depth : Nat}
    {left right : State} →
  DepthEquivalent (suc depth) observe step left right →
  DepthEquivalent depth observe step left right
depthEquivalentMonotone {depth = zero} equivalent = proj₁ equivalent
depthEquivalentMonotone {depth = suc depth} equivalent =
  proj₁ equivalent ,
  (λ action → depthEquivalentMonotone (proj₂ equivalent action))

------------------------------------------------------------------------
-- Concrete four-state calculation.
------------------------------------------------------------------------

data State : Set where
  source memo twin accepting : State

data Action : Set where
  advance : Action

observe : State → Bool
observe source = false
observe memo = false
observe twin = false
observe accepting = true

step : Action → State → State
step advance source = accepting
step advance memo = twin
step advance twin = twin
step advance accepting = accepting

run : List Action → State → State
run [] state = state
run (action ∷ rest) state = run rest (step action state)

record RefinedCode : Set where
  constructor refinedCode
  field
    currentObservation : Bool
    nextObservation : Bool

open RefinedCode public

refineCode : State → RefinedCode
refineCode state = refinedCode (observe state) (observe (step advance state))

currentPartitionStillTooCoarse : observe source ≡ observe memo
currentPartitionStillTooCoarse = refl

firstRefinementSeparatesSourceAndMemo :
  refineCode source ≡ refineCode memo → ⊥
firstRefinementSeparatesSourceAndMemo ()

refinementKeepsMemoAndTwinTogether : refineCode memo ≡ refineCode twin
refinementKeepsMemoAndTwinTogether = refl

stepIsFixedAfterOne : (state : State) →
  step advance (step advance state) ≡ step advance state
stepIsFixedAfterOne source = refl
stepIsFixedAfterOne memo = refl
stepIsFixedAfterOne twin = refl
stepIsFixedAfterOne accepting = refl

runFromFixed :
  (actions : List Action) →
  (state : State) →
  step advance state ≡ state →
  run actions state ≡ state
runFromFixed [] state fixed = refl
runFromFixed (advance ∷ rest) state fixed rewrite fixed =
  runFromFixed rest state fixed

runAfterFirstStable :
  (rest : List Action) →
  (state : State) →
  run (advance ∷ rest) state ≡ step advance state
runAfterFirstStable rest state =
  runFromFixed rest (step advance state) (stepIsFixedAfterOne state)

stableCodeDeterminesEveryTraceObservation :
  {left right : State} →
  refineCode left ≡ refineCode right →
  (actions : List Action) →
  observe (run actions left) ≡ observe (run actions right)
stableCodeDeterminesEveryTraceObservation codeEqual [] =
  cong currentObservation codeEqual
stableCodeDeterminesEveryTraceObservation {left} {right} codeEqual (advance ∷ rest)
  rewrite runAfterFirstStable rest left
        | runAfterFirstStable rest right =
  cong nextObservation codeEqual

stableRefinementIsFutureSafe :
  {left right : State} →
  refineCode left ≡ refineCode right →
  (actions : List Action) →
  observe (run actions left) ≡ observe (run actions right)
stableRefinementIsFutureSafe = stableCodeDeterminesEveryTraceObservation

------------------------------------------------------------------------
-- In this finite machine the refinement stabilizes after one strict split:
-- source separates from memo/twin, while memo and twin remain one canonical
-- future class.  The stable code therefore computes the maximally safe
-- deterministic quotient for this example.
------------------------------------------------------------------------
