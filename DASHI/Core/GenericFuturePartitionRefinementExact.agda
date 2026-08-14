module DASHI.Core.GenericFuturePartitionRefinementExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- GENERIC DETERMINISTIC FUTURE PARTITION REFINEMENT
--
-- P0 is current-observation equality.  P(n+1) additionally requires every
-- one-action successor pair to lie in Pn.  This is the generic recurrence used
-- by finite canonical quotient computation.
------------------------------------------------------------------------

RefinesToDepth :
  ∀ {State Action Observation : Set} →
  Nat →
  (State → Observation) →
  (Action → State → State) →
  State → State → Set
RefinesToDepth zero observe step left right = observe left ≡ observe right
RefinesToDepth (suc depth) observe step left right =
  (observe left ≡ observe right)
  × ((action : Action) →
      RefinesToDepth depth observe step (step action left) (step action right))

refinementMonotone :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {depth : Nat} {left right : State} →
  RefinesToDepth (suc depth) observe step left right →
  RefinesToDepth depth observe step left right
refinementMonotone {depth = zero} refined = proj₁ refined
refinementMonotone {depth = suc depth} refined =
  proj₁ refined , λ action → refinementMonotone (proj₂ refined action)

------------------------------------------------------------------------
-- Fixed point.  Equality of consecutive refinement relations is represented
-- extensionally by implications in both directions.
------------------------------------------------------------------------

record StableAt
    {State Action Observation : Set}
    (depth : Nat)
    (observe : State → Observation)
    (step : Action → State → State) : Set₁ where
  constructor stableAt
  field
    forwardStable :
      ∀ {left right} →
      RefinesToDepth depth observe step left right →
      RefinesToDepth (suc depth) observe step left right
    backwardStable :
      ∀ {left right} →
      RefinesToDepth (suc depth) observe step left right →
      RefinesToDepth depth observe step left right

open StableAt public

stableAtNext :
  ∀ {State Action Observation depth}
    {observe : State → Observation}
    {step : Action → State → State} →
  StableAt depth observe step →
  StableAt (suc depth) observe step
stableAtNext {depth = depth} stable = stableAt nextForward refinementMonotone
  where
    nextForward :
      ∀ {left right} →
      RefinesToDepth (suc depth) observe step left right →
      RefinesToDepth (suc (suc depth)) observe step left right
    nextForward refined =
      proj₁ refined , λ action →
        forwardStable stable (proj₂ refined action)

stablePersists :
  ∀ {State Action Observation depth}
    {observe : State → Observation}
    {step : Action → State → State} →
  StableAt depth observe step →
  (extra : Nat) → StableAt (depth + extra) observe step
stablePersists stable zero rewrite +-identityʳ _ = stable
stablePersists {depth = depth} stable (suc extra)
  rewrite +-suc depth extra =
  stableAtNext (stablePersists stable extra)

------------------------------------------------------------------------
-- Trace observations are already determined by sufficiently deep refinement.
------------------------------------------------------------------------

run :
  ∀ {State Action : Set} →
  (Action → State → State) →
  List Action → State → State
run step [] state = state
run step (action ∷ rest) state = run step rest (step action state)

traceObservationFromDepth :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State}
    (actions : List Action) →
  RefinesToDepth (length actions) observe step left right →
  observe (run step actions left) ≡ observe (run step actions right)
traceObservationFromDepth [] refined = refined
traceObservationFromDepth (action ∷ rest) refined =
  traceObservationFromDepth rest (proj₂ refined action)

------------------------------------------------------------------------
-- Once a depth is stable, a state pair related there is related at every
-- greater finite depth and therefore agrees after every finite action trace.
------------------------------------------------------------------------

stablePairLifts :
  ∀ {State Action Observation depth}
    {observe : State → Observation}
    {step : Action → State → State}
    (stable : StableAt depth observe step)
    {left right : State} →
  RefinesToDepth depth observe step left right →
  (extra : Nat) → RefinesToDepth (depth + extra) observe step left right
stablePairLifts stable related zero rewrite +-identityʳ _ = related
stablePairLifts {depth = depth} stable related (suc extra)
  rewrite +-suc depth extra =
  forwardStable (stablePersists stable extra)
    (stablePairLifts stable related extra)

------------------------------------------------------------------------
-- Boundary: existence of a StableAt depth for every finite State requires the
-- separate finite-partition counting theorem.  The recurrence and fixed-point
-- persistence above do not assume that theorem.
------------------------------------------------------------------------
