module DASHI.Biology.BraidedEmotionTheoryContention where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BraidedEmotionProcessBoundary as Emotion

------------------------------------------------------------------------
-- Typed contention surface.
--
-- This module strengthens the prose-level pluralism in the process boundary.
-- Theories are indexed by explanatory scale and by disputed commitment.  A
-- row may remain locally useful while conflict is preserved explicitly.

data ExplanationScale : Set where
  neuralMechanismScale : ExplanationScale
  bodilyRegulationScale : ExplanationScale
  actionSelectionScale : ExplanationScale
  phenomenologicalScale : ExplanationScale
  interpersonalScale : ExplanationScale
  culturalHistoricalScale : ExplanationScale
  ethicalGovernanceScale : ExplanationScale

data ContentionAxis : Set where
  categoryNaturalKindAxis : ContentionAxis
  biologicalUniversalityAxis : ContentionAxis
  conceptualNecessityAxis : ContentionAxis
  languageConstitutionAxis : ContentionAxis
  neuralSpecificityAxis : ContentionAxis
  worldInvolvementAxis : ContentionAxis
  relationConstitutionAxis : ContentionAxis

data TheoryPosition : Set where
  affirmsPosition : TheoryPosition
  deniesPosition : TheoryPosition
  weakensPosition : TheoryPosition
  underdeterminedPosition : TheoryPosition
  scaleDependentPosition : TheoryPosition

record TheoryScaleRow : Set where
  constructor mkTheoryScaleRow
  field
    theory : Emotion.EmotionTheory
    scale : ExplanationScale
    locallyApplicable : Bool
    globallySufficient : Bool
    applicationReading : String

open TheoryScaleRow public

record TheoryContentionRow : Set where
  constructor mkTheoryContentionRow
  field
    theory : Emotion.EmotionTheory
    axis : ContentionAxis
    position : TheoryPosition
    contentionReading : String

open TheoryContentionRow public

canonicalTheoryScaleRows : List TheoryScaleRow
canonicalTheoryScaleRows =
  mkTheoryScaleRow Emotion.basicDiscreteTheory neuralMechanismScale true false
    "recurrent biological organisation is locally informative but not globally sufficient"
  ∷ mkTheoryScaleRow Emotion.constructionistTheory phenomenologicalScale true false
    "learned categorisation helps explain flexible experience without erasing bodily constraint"
  ∷ mkTheoryScaleRow Emotion.appraisalTheory actionSelectionScale true false
    "goal-relative significance helps explain action selection without exhausting embodiment"
  ∷ mkTheoryScaleRow Emotion.actionReadinessTheory actionSelectionScale true false
    "action preparation is locally central but is not identical with the whole episode"
  ∷ mkTheoryScaleRow Emotion.predictiveProcessingTheory bodilyRegulationScale true false
    "prediction and precision organise regulation but do not settle all semantic questions"
  ∷ mkTheoryScaleRow Emotion.enactiveEcologicalTheory interpersonalScale true false
    "organism-world coordination is locally central without replacing neural mechanism"
  ∷ mkTheoryScaleRow Emotion.socialRelationalTheory culturalHistoricalScale true false
    "relation power and history individuate meaning without replacing organismic continuity"
  ∷ []

canonicalTheoryContentionRows : List TheoryContentionRow
canonicalTheoryContentionRows =
  mkTheoryContentionRow Emotion.basicDiscreteTheory categoryNaturalKindAxis affirmsPosition
    "basic-discrete accounts retain stronger category-kind commitments"
  ∷ mkTheoryContentionRow Emotion.constructionistTheory categoryNaturalKindAxis weakensPosition
    "constructionist accounts weaken fixed natural-kind commitments"
  ∷ mkTheoryContentionRow Emotion.basicDiscreteTheory biologicalUniversalityAxis affirmsPosition
    "basic-discrete accounts predict stronger cross-context biological recurrence"
  ∷ mkTheoryContentionRow Emotion.socialRelationalTheory biologicalUniversalityAxis scaleDependentPosition
    "social-relational accounts treat recurrence as conditioned by relation and history"
  ∷ mkTheoryContentionRow Emotion.constructionistTheory conceptualNecessityAxis affirmsPosition
    "constructionist accounts grant concepts a constitutive role"
  ∷ mkTheoryContentionRow Emotion.actionReadinessTheory conceptualNecessityAxis weakensPosition
    "action-readiness can begin before explicit conceptual classification"
  ∷ mkTheoryContentionRow Emotion.constructionistTheory languageConstitutionAxis scaleDependentPosition
    "language may reshape and scaffold categories without being the only concept carrier"
  ∷ mkTheoryContentionRow Emotion.predictiveProcessingTheory neuralSpecificityAxis underdeterminedPosition
    "predictive language alone underdetermines specific neural implementation"
  ∷ mkTheoryContentionRow Emotion.enactiveEcologicalTheory worldInvolvementAxis affirmsPosition
    "enactive accounts treat world involvement as constitutive rather than merely causal input"
  ∷ mkTheoryContentionRow Emotion.socialRelationalTheory relationConstitutionAxis affirmsPosition
    "social-relational accounts treat some emotion identity as relation-constituted"
  ∷ []

record PreservedContentionReceipt : Set where
  constructor mkPreservedContentionReceipt
  field
    scaleRows : List TheoryScaleRow
    contentionRows : List TheoryContentionRow
    localApplicabilityPreserved : Bool
    globalWinnerDeclared : Bool
    incompatiblePositionsRetained : Bool
    scaleDependenceRetained : Bool
    contentionPreserved : Bool
    contentionPreservedIsTrue : contentionPreserved ≡ true

open PreservedContentionReceipt public

canonicalPreservedContentionReceipt : PreservedContentionReceipt
canonicalPreservedContentionReceipt =
  mkPreservedContentionReceipt
    canonicalTheoryScaleRows
    canonicalTheoryContentionRows
    true
    false
    true
    true
    true
    refl
