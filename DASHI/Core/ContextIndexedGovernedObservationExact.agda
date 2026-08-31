module DASHI.Core.ContextIndexedGovernedObservationExact where

------------------------------------------------------------------------
-- CONTEXT / QUERY INDEXED GOVERNED OBSERVATION SAFETY
--
-- A projection is not intrinsically governance-safe.  The governed coordinates
-- required by a consumer may vary with context and query.  This module lifts
-- the existing active-obligation and consumer-sufficiency patterns to a
-- dependent family of governed observer axes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer

record ContextIndexedGovernedFamily
    (State Context Query Surface : Set)
    (observe : State → Surface) : Set₁ where
  constructor context-indexed-governed-family
  field
    Axis : Set
    Outcome : Axis → Set
    Active : Context → Query → Axis → Set
    consume : (axis : Axis) → State → Outcome axis

open ContextIndexedGovernedFamily public

GovernedSafeFor :
  ∀ {State Context Query Surface}
    {observe : State → Surface} →
  ContextIndexedGovernedFamily State Context Query Surface observe →
  Context → Query → Set
GovernedSafeFor family context query =
  (axis : Axis family) →
  Active family context query axis →
  Consumer.ConsumerSufficient observe (consume family axis)

record ActiveGovernedCollision
    {State Context Query Surface}
    {observe : State → Surface}
    (family : ContextIndexedGovernedFamily State Context Query Surface observe)
    (context : Context)
    (query : Query) : Set₁ where
  constructor active-governed-collision
  field
    axis : Axis family
    axisIsActive : Active family context query axis
    collision :
      Consumer.ConsumerRelevantCollision observe (consume family axis)

open ActiveGovernedCollision public

activeGovernedCollisionBlocksSafety :
  ∀ {State Context Query Surface}
    {observe : State → Surface}
    {family : ContextIndexedGovernedFamily State Context Query Surface observe}
    {context : Context} {query : Query} →
  ActiveGovernedCollision family context query →
  GovernedSafeFor family context query →
  ⊥
activeGovernedCollisionBlocksSafety defect safe =
  Consumer.coarseCollisionBlocksSufficiency
    (collision defect)
    (safe (axis defect) (axisIsActive defect))

-- Requirement inclusion is the variable-rank analogue of required-axis join
-- monotonicity: if every weak requirement is also active in the stronger
-- context/query, safety for the stronger requirement implies safety for the
-- weaker one.
RequirementIncluded :
  ∀ {State Context Query Surface}
    {observe : State → Surface} →
  (family : ContextIndexedGovernedFamily State Context Query Surface observe) →
  Context → Query → Context → Query → Set
RequirementIncluded family weakContext weakQuery strongContext strongQuery =
  (axis : Axis family) →
  Active family weakContext weakQuery axis →
  Active family strongContext strongQuery axis

strongerRequirementSafetyImpliesWeaker :
  ∀ {State Context Query Surface}
    {observe : State → Surface}
    {family : ContextIndexedGovernedFamily State Context Query Surface observe}
    {weakContext strongContext : Context}
    {weakQuery strongQuery : Query} →
  RequirementIncluded family weakContext weakQuery strongContext strongQuery →
  GovernedSafeFor family strongContext strongQuery →
  GovernedSafeFor family weakContext weakQuery
strongerRequirementSafetyImpliesWeaker included strongSafe axis activeWeak =
  strongSafe axis (included axis activeWeak)

-- The converse is intentionally absent: activating a new governed coordinate
-- can expose a consumer-relevant collision invisible to the weaker language.
record ContextIndexedGovernedObservationBoundary : Set where
  field
    governedRequirementsMayVaryByContextAndQuery : Bool
    inactiveAxisCountsAsFailedAxis : Bool
    activeCollisionBlocksSafety : Bool
    strongerSafetyImpliesWeakerUnderRequirementInclusion : Bool
    weakerSafetyAutomaticallyImpliesStrongerSafety : Bool
    oneGloballyFixedGovernanceBundleIsRequired : Bool

canonicalContextIndexedGovernedObservationBoundary :
  ContextIndexedGovernedObservationBoundary
canonicalContextIndexedGovernedObservationBoundary = record
  { governedRequirementsMayVaryByContextAndQuery = true
  ; inactiveAxisCountsAsFailedAxis = false
  ; activeCollisionBlocksSafety = true
  ; strongerSafetyImpliesWeakerUnderRequirementInclusion = true
  ; weakerSafetyAutomaticallyImpliesStrongerSafety = false
  ; oneGloballyFixedGovernanceBundleIsRequired = false
  }
