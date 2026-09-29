module DASHI.Reasoning.Trialectic369Selected3BFullGradeActionMaxCutExact where

------------------------------------------------------------------------
-- SELECTED 3B ACTION MAX-CUT THROUGH THE FULL GRADE-TWO REPRESENTATION
--
-- DASHI CONTRIBUTION
--
-- The canonical linear core currently asks for a faithful constituent-action
-- comparison after inclusion into the full weight-two grade.
--
-- But the existing WeightTwoLinearActionBridge already proves that the
-- constituent Monster action itself intertwines with the SAME full grade-two
-- action.  Therefore the remaining source payment can be stated more naturally
-- as:
--
--   (1) the constituent inclusion is faithful/injective;
--   (2) the selected normalizer action, transported back to the constituent,
--       realizes that same full grade-two action after inclusion.
--
-- Those two receipts compile the previous FaithfulConstituentActionComparison,
-- hence the canonical Selected3B action intertwiner and completion.
--
-- No dimension, character, subgroup name, Fin90 basis, or source identifier
-- manufactures either receipt.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as LinearRep
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Core
import DASHI.Reasoning.Trialectic369Selected3BActionViaFaithfulInclusionExact as Comparison

------------------------------------------------------------------------
-- 1. Faithfulness of the actual constituent inclusion.
------------------------------------------------------------------------

record FaithfulWeightTwoConstituent
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Set₁ where
  field
    inclusionInjective :
      ∀ {left right :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))} →
      WeightTwo.constituentInclusion
        (Core.weightTwoLinearBridge core) left
      ≡
      WeightTwo.constituentInclusion
        (Core.weightTwoLinearBridge core) right
      →
      left ≡ right

open FaithfulWeightTwoConstituent public

------------------------------------------------------------------------
-- 2. Selected action realizes the same full grade-two action.
------------------------------------------------------------------------

fullGradeTwoActionAt :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  Monster →
  Linear.Vector
    (WeightTwo.constituentLinearCarrier
      (Core.weightTwoLinearBridge core)) →
  Linear.Vector
    (LinearRep.linearCarrier
      (WeightTwo.fullWeightTwoLinearRealisation
        (Core.weightTwoLinearBridge core)))
fullGradeTwoActionAt core monster state =
  LinearRep.evaluatedEnd
    (WeightTwo.fullWeightTwoLinearRealisation
      (Core.weightTwoLinearBridge core))
    (GR.action
      (GR.grade
        (GVOA.gradedRepresentation
          (DASHI.Moonshine.MonsterGradedVOABridgeExact.voaAction
            (DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact.gradedAuthority
              (DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact.weld
                (DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact.selectedSource
                  (DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact.attachment
                    (Core.kernelRecognizedSameElementAttachment core)))))))
        2)
      monster)
    (WeightTwo.constituentInclusion
      (Core.weightTwoLinearBridge core) state)

record SelectedNormalizerFullGradeTwoAgreement
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    selectedRealizesFullGradeTwo :
      (normalizer : Single.Normalizer (Core.linearProducer core)) →
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Core.weightTwoLinearBridge core))) →
      fullGradeTwoActionAt
        core
        (Core.normalizerToMonster core normalizer)
        state
      ≡
      WeightTwo.constituentInclusion
        (Core.weightTwoLinearBridge core)
        (Comparison.selectedActionBackOnConstituent
          core normalizer state)

open SelectedNormalizerFullGradeTwoAgreement public

------------------------------------------------------------------------
-- 3. Existing constituent intertwining closes the old comparison.
------------------------------------------------------------------------

actionsAgreeAfterInclusionFromFullGrade :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  SelectedNormalizerFullGradeTwoAgreement core →
  (normalizer : Single.Normalizer (Core.linearProducer core)) →
  (state :
    Linear.Vector
      (WeightTwo.constituentLinearCarrier
        (Core.weightTwoLinearBridge core))) →
  WeightTwo.constituentInclusion (Core.weightTwoLinearBridge core)
    (WeightTwo.constituentAct
      (Core.weightTwoLinearBridge core)
      (Core.normalizerToMonster core normalizer)
      state)
  ≡
  WeightTwo.constituentInclusion (Core.weightTwoLinearBridge core)
    (Comparison.selectedActionBackOnConstituent
      core normalizer state)
actionsAgreeAfterInclusionFromFullGrade core agreement normalizer state =
  trans
    (sym
      (WeightTwo.constituentInclusionIntertwines
        (Core.weightTwoLinearBridge core)
        (Core.normalizerToMonster core normalizer)
        state))
    (selectedRealizesFullGradeTwo agreement normalizer state)

faithfulComparisonFromFullGrade :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  FaithfulWeightTwoConstituent core →
  SelectedNormalizerFullGradeTwoAgreement core →
  Comparison.FaithfulConstituentActionComparison core
faithfulComparisonFromFullGrade core faithful agreement =
  record
    { inclusionInjective = inclusionInjective faithful
    ; actionsAgreeAfterFullGradeTwoInclusion =
        actionsAgreeAfterInclusionFromFullGrade core agreement
    }

canonicalActionIntertwiningFromFullGrade :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  FaithfulWeightTwoConstituent core →
  SelectedNormalizerFullGradeTwoAgreement core →
  Core.CanonicalSelected3BActionIntertwining core
canonicalActionIntertwiningFromFullGrade core faithful agreement =
  Comparison.compileActionIntertwiningFromInclusion
    core
    (faithfulComparisonFromFullGrade core faithful agreement)

canonicalCompletionFromFullGrade :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  FaithfulWeightTwoConstituent core →
  SelectedNormalizerFullGradeTwoAgreement core →
  Core.CanonicalSelected3BLinearCompletion {Monster} {K}
canonicalCompletionFromFullGrade core faithful agreement =
  record
    { core = core
    ; actionIntertwining =
        canonicalActionIntertwiningFromFullGrade
          core faithful agreement
    }

------------------------------------------------------------------------
-- 4. One full-grade counterexample refutes the selected action weld.
------------------------------------------------------------------------

record FullGradeTwoActionCounterexample
    {Monster K : Set}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K})
    : Setω where
  field
    normalizer : Single.Normalizer (Core.linearProducer core)

    state :
      Linear.Vector
        (WeightTwo.constituentLinearCarrier
          (Core.weightTwoLinearBridge core))

    mismatch :
      fullGradeTwoActionAt
        core
        (Core.normalizerToMonster core normalizer)
        state
      ≢
      WeightTwo.constituentInclusion
        (Core.weightTwoLinearBridge core)
        (Comparison.selectedActionBackOnConstituent
          core normalizer state)

open FullGradeTwoActionCounterexample public

fullGradeCounterexampleRejectsAgreement :
  ∀ {Monster K}
    (core : Core.CanonicalSelected3BLinearCore {Monster} {K}) →
  FullGradeTwoActionCounterexample core →
  SelectedNormalizerFullGradeTwoAgreement core →
  ⊥
fullGradeCounterexampleRejectsAgreement core witness agreement =
  mismatch witness
    (selectedRealizesFullGradeTwo
      agreement
      (normalizer witness)
      (state witness))

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data LinearDimensionCreatesFaithfulness : Set where
data SameCarrierCreatesFullGradeActionAgreement : Set where
data CharacterCreatesFullGradeActionAgreement : Set where

dimensionDoesNotCreateFaithfulness :
  LinearDimensionCreatesFaithfulness → ⊥
dimensionDoesNotCreateFaithfulness ()

sameCarrierDoesNotCreateActionAgreement :
  SameCarrierCreatesFullGradeActionAgreement → ⊥
sameCarrierDoesNotCreateActionAgreement ()

characterDoesNotCreateActionAgreement :
  CharacterCreatesFullGradeActionAgreement → ⊥
characterDoesNotCreateActionAgreement ()

------------------------------------------------------------------------
-- 6. Machine-readable frontier.
------------------------------------------------------------------------

record Trialectic369Selected3BFullGradeActionMaxCutBoundary : Set where
  constructor trialectic-369-selected3b-full-grade-action-maxcut-boundary
  field
    constituentMonsterActionAlreadyIntertwinesFullGradeTwo : Bool
    remainingFaithfulInclusionSeparated : Bool
    remainingSelectedFullGradeActionAgreementSeparated : Bool
    oldFaithfulComparisonCompilerOutput : Bool
    canonicalActionIntertwiningCompilerOutput : Bool
    canonicalCompletionCompilerOutput : Bool
    oneFullGradeCounterexampleRejectsAgreement : Bool
    inclusionFaithfulnessInhabitedHere : Bool
    selectedFullGradeAgreementInhabitedHere : Bool
    completionInhabitedHere : Bool

canonicalTrialectic369Selected3BFullGradeActionMaxCutBoundary :
  Trialectic369Selected3BFullGradeActionMaxCutBoundary
canonicalTrialectic369Selected3BFullGradeActionMaxCutBoundary =
  trialectic-369-selected3b-full-grade-action-maxcut-boundary
    true true true true true true true
    false false false
