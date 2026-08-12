module DASHI.Core.DynamicProjectionCompositionExact where

------------------------------------------------------------------------
-- DYNAMIC PROJECTION COMPOSITION
--
-- This is the functional/deterministic composition theorem complementary to
-- the proof-bearing nondeterministic future-language quotient.  When each
-- projection commutes with every consumer action, the composite projection
-- commutes with every action and therefore with every finite action trace.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record ActionDynamics (State Action : Set) : Set₁ where
  constructor actionDynamics
  field
    step : Action → State → State

open ActionDynamics public

runTrace :
  ∀ {State Action} →
  ActionDynamics State Action →
  List Action → State → State
runTrace dynamics [] state = state
runTrace dynamics (action ∷ rest) state =
  runTrace dynamics rest (step dynamics action state)

record DynamicProjection
    {Fine Coarse Action : Set}
    (fineDynamics : ActionDynamics Fine Action)
    (coarseDynamics : ActionDynamics Coarse Action) : Set₁ where
  constructor dynamicProjection
  field
    project : Fine → Coarse
    stepCommutes :
      (action : Action) → (state : Fine) →
      project (step fineDynamics action state)
      ≡ step coarseDynamics action (project state)

open DynamicProjection public

traceCommutes :
  ∀ {Fine Coarse Action}
    {fineDynamics : ActionDynamics Fine Action}
    {coarseDynamics : ActionDynamics Coarse Action}
    (projection : DynamicProjection fineDynamics coarseDynamics)
    (actions : List Action)
    (state : Fine) →
  project projection (runTrace fineDynamics actions state)
  ≡ runTrace coarseDynamics actions (project projection state)
traceCommutes projection [] state = refl
traceCommutes {fineDynamics = fineDynamics} {coarseDynamics = coarseDynamics}
  projection (action ∷ rest) state =
  trans
    (traceCommutes projection rest (step fineDynamics action state))
    (cong (runTrace coarseDynamics rest)
      (stepCommutes projection action state))

composeDynamicProjection :
  ∀ {X Y Z Action}
    {dX : ActionDynamics X Action}
    {dY : ActionDynamics Y Action}
    {dZ : ActionDynamics Z Action} →
  DynamicProjection dX dY →
  DynamicProjection dY dZ →
  DynamicProjection dX dZ
composeDynamicProjection first second =
  dynamicProjection
    (λ x → project second (project first x))
    (λ action state →
      trans
        (cong (project second) (stepCommutes first action state))
        (stepCommutes second action (project first state)))

compositeTraceCommutes :
  ∀ {X Y Z Action}
    {dX : ActionDynamics X Action}
    {dY : ActionDynamics Y Action}
    {dZ : ActionDynamics Z Action}
    (first : DynamicProjection dX dY)
    (second : DynamicProjection dY dZ)
    (actions : List Action)
    (state : X) →
  project second (project first (runTrace dX actions state))
  ≡ runTrace dZ actions (project second (project first state))
compositeTraceCommutes first second actions state =
  traceCommutes (composeDynamicProjection first second) actions state

------------------------------------------------------------------------
-- Kernel consequence: equal composite observations remain equal after every
-- finite trace.  Quotient compatibility and metric contraction remain distinct
-- obligations; this module proves only the former.
------------------------------------------------------------------------

compositeEqualNowGivesEqualAfterTrace :
  ∀ {X Y Z Action}
    {dX : ActionDynamics X Action}
    {dY : ActionDynamics Y Action}
    {dZ : ActionDynamics Z Action}
    (first : DynamicProjection dX dY)
    (second : DynamicProjection dY dZ)
    (actions : List Action)
    {left right : X} →
  project second (project first left)
  ≡ project second (project first right) →
  project second (project first (runTrace dX actions left))
  ≡ project second (project first (runTrace dX actions right))
compositeEqualNowGivesEqualAfterTrace
  {dZ = dZ} first second actions {left} {right} same =
  trans
    (compositeTraceCommutes first second actions left)
    (trans
      (cong (runTrace dZ actions) same)
      (sym (compositeTraceCommutes first second actions right)))
