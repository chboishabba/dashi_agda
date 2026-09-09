{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedRegularESourceCompilerRound238Exact where

------------------------------------------------------------------------
-- ROUND238 / SELECTED SOURCE SEMANTICS -> REGULAR-E REALIZATION DIRECTLY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource
import DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredContinuationRound222Exact as R222
import DASHI.Physics.YangMills.BalabanSelectedDensitySemanticsRound237Exact as Selected

record SelectedSourceFixedCMP116Localization
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (semantics : Selected.SelectedEffectiveDensitySemantics inputs) : Set₁ where
  field
    Volume Tangent Component : Set

    components : Nat → Volume → List Component
    physicalLocalizedActivity :
      Nat → Volume → Component → Selected.Background semantics → ℝ

    selectedPotentialIsLocalizedCompositeSum :
      ∀ scale volume background →
      Selected.selectedPotential semantics scale background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (physicalLocalizedActivity scale volume)
            (components scale volume))
          background

open SelectedSourceFixedCMP116Localization public

record SelectedRegularESemanticWeld
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (projection : ESource.CMP119RegularESourceProjection inputs)
    (semantics : Selected.SelectedEffectiveDensitySemantics inputs) : Set₁ where
  field
    evaluateRegularE :
      ESource.RegularTerm projection → Selected.Background semantics → ℝ

    selectedSourcePotentialIsRegularE : ∀ scale background →
      Selected.selectedPotential semantics scale background
      ≡ evaluateRegularE (ESource.selectedRegularE projection scale) background

open SelectedRegularESemanticWeld public

compilePreferredRegularERealization :
  ∀ {trajectory split inputs projection semantics} →
  (localization : SelectedSourceFixedCMP116Localization
    {trajectory = trajectory} {split = split} {inputs = inputs} semantics) →
  SelectedRegularESemanticWeld projection semantics →
  R222.PreferredRegularERealization projection
compilePreferredRegularERealization {projection = projection} {semantics = semantics}
    localization weld = record
  { R222.PreferredRegularERealization.Background = Selected.Background semantics
  ; R222.PreferredRegularERealization.Volume = Volume localization
  ; R222.PreferredRegularERealization.Tangent = Tangent localization
  ; R222.PreferredRegularERealization.Component = Component localization
  ; R222.PreferredRegularERealization.evaluateRegularE = evaluateRegularE weld
  ; R222.PreferredRegularERealization.components = components localization
  ; R222.PreferredRegularERealization.localizedRegularActivity =
      physicalLocalizedActivity localization
  ; R222.PreferredRegularERealization.selectedRegularEIsLocalizedCompositeSum =
      λ scale volume background →
        trans
          (sym (selectedSourcePotentialIsRegularE weld scale background))
          (selectedPotentialIsLocalizedCompositeSum
            localization scale volume background)
  }

selectedSourceToRegularECompilerLevel : ProofLevel
selectedSourceToRegularECompilerLevel = machineChecked

literalSelectedCMP116LocalizationLevel : ProofLevel
literalSelectedCMP116LocalizationLevel = conditional

literalSelectedSourcePotentialIsCMP119RegularELevel : ProofLevel
literalSelectedSourcePotentialIsCMP119RegularELevel = conditional
