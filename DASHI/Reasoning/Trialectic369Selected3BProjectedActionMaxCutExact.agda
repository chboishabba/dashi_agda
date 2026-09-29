module DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact where

------------------------------------------------------------------------
-- SELECTED 3B ACTION AS PROJECTION OF THE SAME FULL GRADE-TWO ACTION
--
-- DASHI CONTRIBUTION
--
-- Given an actual constituent retraction
--
--   p : V_2 -> V_196883
--   p (i v) = v,
--
-- the existing WeightTwoLinearActionBridge already proves
--
--   fullGrade(g, i v) = i (constituentAct(g,v)).
--
-- Applying p therefore recovers the constituent action exactly.
--
-- The remaining selected-3B source theorem can consequently be stated in the
-- natural direct-summand form:
--
--   selectedAction(v)
--     = p (fullGrade(normalizerToMonster(n), i v)).
--
-- This single projected-action equation plus the retraction compiles the
-- canonical selected-3B action intertwiner and completion.  No separate
-- inclusion-injectivity receipt is needed on this route.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369Selected3BActionViaFaithfulInclusionExact as Comparison
import DASHI.Reasoning.Trialectic369Selected3BFullGradeActionMaxCutExact as FullGrade
import DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact as Retraction

------------------------------------------------------------------------
-- 1. Projection of the full grade-two action recovers constituent action.
------------------------------------------------------------------------

projectedFullGradeRecoversConstituent :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (retraction : Retraction.ConstituentRetraction core) →
  (normalizer : Single.Normalizer (Core.linearProducer core)) →
  (state :
    Linear.Vector
      (WeightTwo.constituentLinearCarrier
        (Core.weightTwoLinearBridge core))) →
  Retraction.projectToConstituent retraction
    (FullGrade.fullGradeTwoActionAt
      core
      (Core.normalizerToMonster core normalizer)
      state)
  ≡
  WeightTwo.constituentAct
    (Core.weightTwoLinearBridge core)
    (Core.normalizerToMonster core normalizer)
    state
projectedFullGradeRecoversConstituent core retraction normalizer state =
  trans
    (cong
      (Retraction.projectToConstituent retraction)
      (WeightTwo.constituentInclusionIntertwines
        (Core.weightTwoLinearBridge core)
        (Core.normalizerToMonster core normalizer)
        state))
    (Retraction.leftInverse retraction
      (WeightTwo.constituentAct
        (Core.weightTwoLinearBridge core)
        (Core.normalizerToMonster core normalizer)
        state))

------------------------------------------------------------------------
-- 2. One source-shaped projected-action equation.
------------------------------------------------------------------------

record SelectedActionIsProjectedFullGrade
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    (retraction : Retraction.ConstituentRetraction core)
    : Setω where
  field
    selectedEqualsProjectedFullGrade :
      (normalizer : Single.Normalizer (Core.linearProducer core)) →
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))) →
      Comparison.selectedActionBackOnConstituent
        core normalizer state
      ≡
      Retraction.projectToConstituent retraction
        (FullGrade.fullGradeTwoActionAt
          core
          (Core.normalizerToMonster core normalizer)
          state)

open SelectedActionIsProjectedFullGrade public

------------------------------------------------------------------------
-- 3. Projected-action equation closes the canonical same-action weld.
------------------------------------------------------------------------

constituentActionEqualsSelected :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (retraction : Retraction.ConstituentRetraction core) →
  SelectedActionIsProjectedFullGrade core retraction →
  (normalizer : Single.Normalizer (Core.linearProducer core)) →
  (state :
    Linear.Vector
      (WeightTwo.constituentLinearCarrier
        (Core.weightTwoLinearBridge core))) →
  WeightTwo.constituentAct
    (Core.weightTwoLinearBridge core)
    (Core.normalizerToMonster core normalizer)
    state
  ≡
  Comparison.selectedActionBackOnConstituent
    core normalizer state
constituentActionEqualsSelected core retraction projected normalizer state =
  trans
    (sym
      (projectedFullGradeRecoversConstituent
        core retraction normalizer state))
    (sym
      (selectedEqualsProjectedFullGrade
        projected normalizer state))

canonicalActionIntertwiningFromProjectedAction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (retraction : Retraction.ConstituentRetraction core) →
  SelectedActionIsProjectedFullGrade core retraction →
  Core.CanonicalSelected3BActionIntertwining core
canonicalActionIntertwiningFromProjectedAction core retraction projected =
  record
    { intertwines = λ normalizer state →
        FullGrade.transportForwardComparison
          (Core.constituentCarrierIsSelectedState core)
          (WeightTwo.constituentAct
            (Core.weightTwoLinearBridge core)
            (Core.normalizerToMonster core normalizer)
            state)
          (DASHI.Moonshine.Monster3BCentralCharacterInertiaExact.act
            (Single.normalizerAction (Core.linearProducer core))
            normalizer
            (FullGrade.transportForward
              (Core.constituentCarrierIsSelectedState core)
              state))
          (constituentActionEqualsSelected
            core retraction projected normalizer state)
    }

canonicalCompletionFromProjectedAction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (retraction : Retraction.ConstituentRetraction core) →
  SelectedActionIsProjectedFullGrade core retraction →
  Core.CanonicalSelected3BLinearCompletion {Monster} {K}
canonicalCompletionFromProjectedAction core retraction projected =
  record
    { core = core
    ; actionIntertwining =
        canonicalActionIntertwiningFromProjectedAction
          core retraction projected
    }

------------------------------------------------------------------------
-- 4. One source counterexample rejects the projected route.
------------------------------------------------------------------------

record ProjectedActionCounterexample
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    (retraction : Retraction.ConstituentRetraction core)
    : Setω where
  field
    normalizer : Single.Normalizer (Core.linearProducer core)
    state :
      Linear.Vector
        (WeightTwo.constituentLinearCarrier
          (Core.weightTwoLinearBridge core))

    mismatch :
      Comparison.selectedActionBackOnConstituent
        core normalizer state
      ≢
      Retraction.projectToConstituent retraction
        (FullGrade.fullGradeTwoActionAt
          core
          (Core.normalizerToMonster core normalizer)
          state)

open ProjectedActionCounterexample public

projectedCounterexampleRejectsReceipt :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (retraction : Retraction.ConstituentRetraction core) →
  ProjectedActionCounterexample core retraction →
  SelectedActionIsProjectedFullGrade core retraction →
  ⊥
projectedCounterexampleRejectsReceipt core retraction witness receipt =
  mismatch witness
    (selectedEqualsProjectedFullGrade
      receipt
      (normalizer witness)
      (state witness))

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data DirectSumDimensionCreatesProjectedAction : Set where
data CoordinateRetractionCreatesProjectedLinearAction : Set where
data CharacterCreatesProjectedAction : Set where

dimensionDoesNotCreateProjectedAction :
  DirectSumDimensionCreatesProjectedAction → ⊥
dimensionDoesNotCreateProjectedAction ()

coordinateRetractionDoesNotCreateProjectedAction :
  CoordinateRetractionCreatesProjectedLinearAction → ⊥
coordinateRetractionDoesNotCreateProjectedAction ()

characterDoesNotCreateProjectedAction :
  CharacterCreatesProjectedAction → ⊥
characterDoesNotCreateProjectedAction ()

------------------------------------------------------------------------
-- 6. Machine-readable frontier.
------------------------------------------------------------------------

record Trialectic369Selected3BProjectedActionMaxCutBoundary : Set where
  constructor trialectic-369-selected3b-projected-action-maxcut-boundary
  field
    fullGradeProjectionRecoversConstituentAction : Bool
    separateInclusionInjectivityNotRequiredOnProjectedRoute : Bool
    oneProjectedActionEquationSuffices : Bool
    canonicalActionCompilerOwned : Bool
    canonicalCompletionCompilerOwned : Bool
    actualLinearRetractionInhabitedHere : Bool
    actualProjectedActionEquationInhabitedHere : Bool
    canonicalCompletionInhabitedHere : Bool

canonicalTrialectic369Selected3BProjectedActionMaxCutBoundary :
  Trialectic369Selected3BProjectedActionMaxCutBoundary
canonicalTrialectic369Selected3BProjectedActionMaxCutBoundary =
  trialectic-369-selected3b-projected-action-maxcut-boundary
    true true true true true
    false false false
