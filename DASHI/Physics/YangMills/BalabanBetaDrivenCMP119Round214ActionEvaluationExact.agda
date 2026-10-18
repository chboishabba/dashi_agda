module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119Round214ActionEvaluationExact where

------------------------------------------------------------------------
-- ROUND219 ACTION CARRIER -> ROUND214 SOURCE-AUTHORIZED ACTION EVALUATION
--
-- B1a should not be a freely chosen
--
--   Action -> SlowField -> EffectiveAction
--
-- map inside the Gate4 generated-action lane.
--
-- This owner fixes the interpretation of the SAME Round219 Action carrier at
-- the CMP119/Round214 source boundary:
--
--   actionOfDensity (densityAt k) = effectiveActionAt k
--
-- and evaluates that action on the Round214 background carrier in R.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119DensityEffectiveActionProjectionRound214Exact as R214

record BetaDrivenCMP119Round214ActionEvaluation
    {trajectory split}
    (source :
      Beta.BetaDrivenCompleteDensityInputs
        {trajectory = trajectory} {split = split})
    (family : R219.BetaDrivenCMP119ResidualFamily source) : Set₁ where
  field
    Background : Set

    actionOfDensity :
      Beta.Density source → R219.Action family

    evaluateAction :
      R219.Action family → Background → ℝ

    selectedActionIsFamilyAction : ∀ cutoff →
      actionOfDensity (Beta.densityAt source cutoff)
      ≡ R219.effectiveActionAt family cutoff

    IsCMP119Sect2EffectiveActionProjection :
      Nat → Beta.Density source → (Background → ℝ) → Set

    selectedActionHasSourceAuthority : ∀ cutoff →
      IsCMP119Sect2EffectiveActionProjection cutoff
        (Beta.densityAt source cutoff)
        (λ background →
          evaluateAction
            (R219.effectiveActionAt family cutoff)
            background)

open BetaDrivenCMP119Round214ActionEvaluation public

asRound214CompleteDensityActionRepresentation :
  ∀ {trajectory split source family} →
  BetaDrivenCMP119Round214ActionEvaluation
    {trajectory = trajectory} {split = split}
    source family →
  R214.CMP119CompleteDensityActionRepresentation source
asRound214CompleteDensityActionRepresentation interpretation = record
  { R214.CMP119CompleteDensityActionRepresentation.Background =
      Background interpretation
  ; R214.CMP119CompleteDensityActionRepresentation.effectiveActionOfDensity =
      λ density background →
        evaluateAction interpretation
          (actionOfDensity interpretation density)
          background
  ; R214.CMP119CompleteDensityActionRepresentation.IsCMP119Sect2EffectiveActionProjection =
      IsCMP119Sect2EffectiveActionProjection interpretation
  ; R214.CMP119CompleteDensityActionRepresentation.selectedDensityActionIsSourceProjection =
      λ cutoff →
        selectedAuthority cutoff
  }
  where
  selectedAuthority : ∀ cutoff →
    IsCMP119Sect2EffectiveActionProjection interpretation cutoff
      (Beta.densityAt source cutoff)
      (λ background →
        evaluateAction interpretation
          (actionOfDensity interpretation
            (Beta.densityAt source cutoff))
          background)
  selectedAuthority cutoff
    rewrite selectedActionIsFamilyAction interpretation cutoff =
      selectedActionHasSourceAuthority interpretation cutoff

selectedRound219ActionEvaluationIsRound214SelectedAction :
  ∀ {trajectory split source family}
    (interpretation :
      BetaDrivenCMP119Round214ActionEvaluation
        {trajectory = trajectory} {split = split}
        source family)
    cutoff background →
  evaluateAction interpretation
    (R219.effectiveActionAt family cutoff)
    background
  ≡
  R214.selectedEffectiveAction
    (asRound214CompleteDensityActionRepresentation interpretation)
    cutoff
    background
selectedRound219ActionEvaluationIsRound214SelectedAction
  interpretation cutoff background
  rewrite selectedActionIsFamilyAction interpretation cutoff =
    Agda.Builtin.Equality.refl

round219Round214ActionEvaluationCompilerLevel : ProofLevel
round219Round214ActionEvaluationCompilerLevel = machineChecked

round219ActionIsRound214SelectedActionCompilerLevel : ProofLevel
round219ActionIsRound214SelectedActionCompilerLevel = machineChecked

-- B1a source leaf: instantiate the action-of-density map and real evaluation
-- from the literal CMP119 action carrier with Round214 source authority.
literalRound219Round214ActionEvaluationLevel : ProofLevel
literalRound219Round214ActionEvaluationLevel = conditional
