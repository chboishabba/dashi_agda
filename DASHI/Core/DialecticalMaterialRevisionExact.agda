module DASHI.Core.DialecticalMaterialRevisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Core.ContextualDialecticRoleExact as Dialectic

------------------------------------------------------------------------
-- DIALECTICAL / MATERIAL REVISION
--
-- This is a DASHI generic construction, not an attribution of the formal API
-- to Marx or Hegel.  Existing source-bounded Marx/Hegel owners remain the
-- authority for historical propositions.
--
-- The reusable point is structural:
--   retained history may grow monotonically;
--   the currently justified relation/role/conclusion need not;
--   changing material conditions may activate a previously latent tension;
--   frame-relative dialectic role is not an intrinsic property of an entity.
------------------------------------------------------------------------

data TensionState : Set where
  latentTension activeTension transformedTension : TensionState

data MaterialCondition : Set where
  lowPressure highPressure reorganisedCondition : MaterialCondition

data CurrentPosition : Set where
  stablePosition contestedPosition transformedPosition : CurrentPosition

record MaterialRevisionSystem : Set₁ where
  constructor material-revision-system
  field
    condition : Set
    history : Set
    position : Set
    tension : Set
    appendCondition : history → condition → history
    positionAt : history → position
    tensionAt : history → tension

open MaterialRevisionSystem public

record MaterialContradictionActivation
    (system : MaterialRevisionSystem) : Set₁ where
  constructor material-contradiction-activation
  field
    before : history system
    changedCondition : condition system
    beforeTension afterTension : tension system
    beforePosition afterPosition : position system
    beforeTensionMatches : tensionAt system before ≡ beforeTension
    afterTensionMatches :
      tensionAt system (appendCondition system before changedCondition) ≡ afterTension
    beforePositionMatches : positionAt system before ≡ beforePosition
    afterPositionMatches :
      positionAt system (appendCondition system before changedCondition) ≡ afterPosition
    tensionChanges : beforeTension ≡ afterTension → ⊥
    positionChanges : beforePosition ≡ afterPosition → ⊥

open MaterialContradictionActivation public

------------------------------------------------------------------------
-- Exact finite fixture: history is retained, but a changed material condition
-- activates a tension and revises the present position.
------------------------------------------------------------------------

data FixtureHistory : Set where
  lowPressureHistory highPressureHistory reorganisedHistory : FixtureHistory

appendFixture : FixtureHistory → MaterialCondition → FixtureHistory
appendFixture lowPressureHistory lowPressure = lowPressureHistory
appendFixture lowPressureHistory highPressure = highPressureHistory
appendFixture lowPressureHistory reorganisedCondition = reorganisedHistory
appendFixture highPressureHistory reorganisedCondition = reorganisedHistory
appendFixture highPressureHistory _ = highPressureHistory
appendFixture reorganisedHistory _ = reorganisedHistory

fixturePosition : FixtureHistory → CurrentPosition
fixturePosition lowPressureHistory = stablePosition
fixturePosition highPressureHistory = contestedPosition
fixturePosition reorganisedHistory = transformedPosition

fixtureTension : FixtureHistory → TensionState
fixtureTension lowPressureHistory = latentTension
fixtureTension highPressureHistory = activeTension
fixtureTension reorganisedHistory = transformedTension

fixtureSystem : MaterialRevisionSystem
fixtureSystem = material-revision-system
  MaterialCondition FixtureHistory CurrentPosition TensionState
  appendFixture fixturePosition fixtureTension

canonicalActivation : MaterialContradictionActivation fixtureSystem
canonicalActivation = material-contradiction-activation
  lowPressureHistory highPressure
  latentTension activeTension
  stablePosition contestedPosition
  refl refl refl refl
  (λ ()) (λ ())

------------------------------------------------------------------------
-- Cross-pollination with append-only evidence revision.
------------------------------------------------------------------------

appendOnlyHistoryNeedNotGiveMonotoneConclusion :
  Revision.AppendOnlyEvidenceRevisionBoundary
appendOnlyHistoryNeedNotGiveMonotoneConclusion =
  Revision.canonicalAppendOnlyEvidenceRevisionBoundary

------------------------------------------------------------------------
-- Cross-pollination with frame-relative dialectic role.
------------------------------------------------------------------------

contextualRoleBoundary : Dialectic.ContextualDialecticRoleBoundary
contextualRoleBoundary = Dialectic.canonicalContextualDialecticRoleBoundary

record DialecticalMaterialRevisionBoundary : Set where
  constructor dialectical-material-revision-boundary
  field
    retainedHistoryImpliesMonotoneCurrentConclusion : Bool
    changedMaterialConditionMayActivateTension : Bool
    activatedTensionRequiresDeletingEarlierEvidence : Bool
    dialecticRoleIsIntrinsicToEntity : Bool
    materialChangeAloneProvesHistoricalMarxistInterpretation : Bool

canonicalDialecticalMaterialRevisionBoundary : DialecticalMaterialRevisionBoundary
canonicalDialecticalMaterialRevisionBoundary =
  dialectical-material-revision-boundary
    false true false false false
