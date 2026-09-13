{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRegularEPointwiseSemanticsRound239Exact where

------------------------------------------------------------------------
-- ROUND239 / SOURCE REGULAR-E POINTWISE SEMANTICS IS THE TRUE BC1 INPUT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource
import DASHI.Physics.YangMills.BalabanSelectedDensitySemanticsRound237Exact as Selected
import DASHI.Physics.YangMills.BalabanSelectedRegularESourceCompilerRound238Exact as R238

record CMP119RegularEPointwiseSemantics
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (projection : ESource.CMP119RegularESourceProjection inputs) : Set₁ where
  field
    Background : Set

    evaluateRegularE : ESource.RegularTerm projection → Background → ℝ

    IsLiteralRegularEEvaluation :
      ESource.RegularTerm projection → (Background → ℝ) → Set

    selectedRegularEEvaluationIsLiteral : ∀ scale →
      IsLiteralRegularEEvaluation
        (ESource.selectedRegularE projection scale)
        (evaluateRegularE (ESource.selectedRegularE projection scale))

open CMP119RegularEPointwiseSemantics public

record SelectedMeaningWitness
    {trajectory split inputs projection}
    (semantics : CMP119RegularEPointwiseSemantics
      {trajectory = trajectory} {split = split} {inputs = inputs} projection)
    (scale : Nat)
    (potential : Background semantics → ℝ) : Set₁ where
  field
    regularEIsSourceCoordinate :
      ESource.IsCMP119Section2RegularE projection scale
        (Flow.densityAt inputs scale)
        (ESource.selectedRegularE projection scale)

    potentialIsLiteralRegularEEvaluation :
      potential
      ≡ evaluateRegularE semantics (ESource.selectedRegularE projection scale)

open SelectedMeaningWitness public

asSelectedEffectiveDensitySemantics :
  ∀ {trajectory split inputs projection} →
  CMP119RegularEPointwiseSemantics
    {trajectory = trajectory} {split = split} {inputs = inputs} projection →
  Selected.SelectedEffectiveDensitySemantics inputs
asSelectedEffectiveDensitySemantics {inputs = inputs} {projection = projection}
    semantics = record
  { Selected.SelectedEffectiveDensitySemantics.Background = Background semantics
  ; Selected.SelectedEffectiveDensitySemantics.selectedPotential =
      λ scale → evaluateRegularE semantics (ESource.selectedRegularE projection scale)
  ; Selected.SelectedEffectiveDensitySemantics.IsSourceMeaningOfSelectedDensity =
      SelectedMeaningWitness semantics
  ; Selected.SelectedEffectiveDensitySemantics.selectedPotentialHasSourceMeaning =
      λ scale → record
        { SelectedMeaningWitness.regularEIsSourceCoordinate =
            ESource.selectedRegularEHasSourceAuthority projection scale
        ; SelectedMeaningWitness.potentialIsLiteralRegularEEvaluation = refl
        }
  }

asSelectedRegularESemanticWeld :
  ∀ {trajectory split inputs projection}
    (semantics : CMP119RegularEPointwiseSemantics
      {trajectory = trajectory} {split = split} {inputs = inputs} projection) →
  R238.SelectedRegularESemanticWeld
    projection (asSelectedEffectiveDensitySemantics semantics)
asSelectedRegularESemanticWeld semantics = record
  { R238.SelectedRegularESemanticWeld.evaluateRegularE = evaluateRegularE semantics
  ; R238.SelectedRegularESemanticWeld.selectedSourcePotentialIsRegularE =
      λ _ _ → refl
  }

regularEPointwiseToSelectedSemanticsCompilerLevel : ProofLevel
regularEPointwiseToSelectedSemanticsCompilerLevel = machineChecked

regularEPointwiseSelectedWeldLevel : ProofLevel
regularEPointwiseSelectedWeldLevel = machineChecked

-- Preferred source leaf after the recut: give the literal CMP119 regular-E
-- carrier its source-fixed pointwise evaluation on the physical background
-- carrier.  Selected density semantics and the regular-E equality are then
-- generated, not separately postulated.
literalCMP119RegularEPointwiseSemanticsLevel : ProofLevel
literalCMP119RegularEPointwiseSemanticsLevel = conditional
