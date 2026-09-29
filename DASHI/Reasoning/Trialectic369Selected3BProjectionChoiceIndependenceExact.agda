module DASHI.Reasoning.Trialectic369Selected3BProjectionChoiceIndependenceExact where

------------------------------------------------------------------------
-- SELECTED 3B PROJECTED-ACTION RECOGNITION IS RETRACTION-INDEPENDENT
--
-- DASHI theorem; not a claim that an arithmetic/VOA retraction exists.
--
-- The weight-two action preserves the included 196883 constituent.  Therefore
-- ANY two left inverses of that inclusion agree on the full-grade image of a
-- constituent vector.  In particular, the projected-action recognition
-- equation is equivalent for any two constituent retractions.
--
-- This removes projection choice as an independent recognition obstruction.
-- Remaining source leaves: an ACTUAL retraction and the intrinsic same-action
-- equation for the source-selected 3B element.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact as Retraction
import DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact as Projected
import DASHI.Reasoning.Trialectic369Selected3BActionViaFaithfulInclusionExact as Comparison

------------------------------------------------------------------------
-- 1. Any pair of genuine left inverses agrees on the same full-grade action.
------------------------------------------------------------------------

projectedActionIndependentOfRetraction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (first second : Retraction.ConstituentRetraction core) →
  (normalizer : Single.Normalizer (Core.linearProducer core)) →
  (state :
    Linear.Vector
      (WeightTwo.constituentLinearCarrier
        (Core.weightTwoLinearBridge core))) →
  Retraction.projectToConstituent first
    (Projected.FullGrade.fullGradeTwoActionAt
      core
      (Core.normalizerToMonster core normalizer)
      state)
  ≡
  Retraction.projectToConstituent second
    (Projected.FullGrade.fullGradeTwoActionAt
      core
      (Core.normalizerToMonster core normalizer)
      state)
projectedActionIndependentOfRetraction core first second normalizer state =
  trans
    (Projected.projectedFullGradeRecoversConstituent
      core first normalizer state)
    (sym
      (Projected.projectedFullGradeRecoversConstituent
        core second normalizer state))

------------------------------------------------------------------------
-- 2. Recognition transports between ANY two valid retractions.
------------------------------------------------------------------------

projectedRecognitionIndependentOfRetraction :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (first second : Retraction.ConstituentRetraction core) →
  Projected.SelectedActionIsProjectedFullGrade core first →
  Projected.SelectedActionIsProjectedFullGrade core second
projectedRecognitionIndependentOfRetraction core first second recognition =
  record
    { selectedEqualsProjectedFullGrade = λ normalizer state →
        trans
          (Projected.selectedEqualsProjectedFullGrade
            recognition normalizer state)
          (projectedActionIndependentOfRetraction
            core first second normalizer state)
    }

projectedRecognitionTransportBack :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (first second : Retraction.ConstituentRetraction core) →
  Projected.SelectedActionIsProjectedFullGrade core second →
  Projected.SelectedActionIsProjectedFullGrade core first
projectedRecognitionTransportBack core first second =
  projectedRecognitionIndependentOfRetraction core second first

------------------------------------------------------------------------
-- 3. Source-facing invariant formulation.
------------------------------------------------------------------------

record SelectedEqualsIntrinsicConstituentAction
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    sameAction :
      (normalizer : Single.Normalizer (Core.linearProducer core)) →
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))) →
      Comparison.selectedActionBackOnConstituent core normalizer state
      ≡
      WeightTwo.constituentAct
        (Core.weightTwoLinearBridge core)
        (Core.normalizerToMonster core normalizer)
        state

open SelectedEqualsIntrinsicConstituentAction public

intrinsicFromProjected :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (retraction : Retraction.ConstituentRetraction core) →
  Projected.SelectedActionIsProjectedFullGrade core retraction →
  SelectedEqualsIntrinsicConstituentAction core
intrinsicFromProjected core retraction receipt =
  record
    { sameAction = λ normalizer state →
        trans
          (Projected.selectedEqualsProjectedFullGrade
            receipt normalizer state)
          (Projected.projectedFullGradeRecoversConstituent
            core retraction normalizer state)
    }

projectedFromIntrinsic :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  (retraction : Retraction.ConstituentRetraction core) →
  SelectedEqualsIntrinsicConstituentAction core →
  Projected.SelectedActionIsProjectedFullGrade core retraction
projectedFromIntrinsic core retraction receipt =
  record
    { selectedEqualsProjectedFullGrade = λ normalizer state →
        trans
          (sameAction receipt normalizer state)
          (sym
            (Projected.projectedFullGradeRecoversConstituent
              core retraction normalizer state))
    }

------------------------------------------------------------------------
-- 4. Checked status boundary: no actual source theorem is constructed.
------------------------------------------------------------------------

record Selected3BProjectionChoiceIndependenceBoundary : Set where
  constructor selected3b-projection-choice-independence-boundary
  field
    anyTwoRetractionsAgreeOnSelectedFullGradeImages : Bool
    projectedRecognitionTransportedBothWays : Bool
    intrinsicSameActionEquivalentGivenRetraction : Bool
    actualSourceRetractionConstructedHere : Bool
    actualMonsterSameActionConstructedHere : Bool

canonicalSelected3BProjectionChoiceIndependenceBoundary :
  Selected3BProjectionChoiceIndependenceBoundary
canonicalSelected3BProjectionChoiceIndependenceBoundary =
  selected3b-projection-choice-independence-boundary
    true true true false false
