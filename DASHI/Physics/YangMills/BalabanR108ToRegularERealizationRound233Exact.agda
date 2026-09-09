{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanR108ToRegularERealizationRound233Exact where

------------------------------------------------------------------------
-- ROUND233 / REUSE R108 LOCALIZATION; DO NOT REBUILD CMP116 COMPONENTS
--
-- R108 already owns the beta-driven localized effective-action family:
-- background/tangent/component carriers, localized activities, their finite
-- composite-sum theorem, and the common analytic radius.
--
-- Once the source-fixed density potential on the selected beta-driven density
-- is identified with evaluation of the literal CMP119 regular E_k coordinate,
-- the preferred Round222 regular-E realization is generated mechanically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource
import DASHI.Physics.YangMills.BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact as R108
import DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredContinuationRound222Exact as R222

record R108RegularESemanticWeld
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (projection : ESource.CMP119RegularESourceProjection inputs)
    (localized : R108.BetaDrivenLocalizedEffectiveActionFamily inputs) : Set₁ where
  field
    evaluateRegularE :
      ESource.RegularTerm projection → R108.Background localized → ℝ

    selectedDensityPotentialIsRegularE : ∀ scale background →
      R108.potentialOfDensity localized (Flow.densityAt inputs scale) background
      ≡ evaluateRegularE (ESource.selectedRegularE projection scale) background

open R108RegularESemanticWeld public

asPreferredRegularERealization :
  ∀ {trajectory split inputs projection localized} →
  R108RegularESemanticWeld
    {trajectory = trajectory} {split = split} {inputs = inputs}
    projection localized →
  R222.PreferredRegularERealization projection
asPreferredRegularERealization {projection = projection} {localized = localized} weld = record
  { R222.PreferredRegularERealization.Background = R108.Background localized
  ; R222.PreferredRegularERealization.Volume = R108.Volume localized
  ; R222.PreferredRegularERealization.Tangent = R108.Tangent localized
  ; R222.PreferredRegularERealization.Component = R108.Component localized
  ; R222.PreferredRegularERealization.evaluateRegularE = evaluateRegularE weld
  ; R222.PreferredRegularERealization.components = R108.components localized
  ; R222.PreferredRegularERealization.localizedRegularActivity =
      R108.physicalLocalizedActivity localized
  ; R222.PreferredRegularERealization.selectedRegularEIsLocalizedCompositeSum =
      λ scale volume background →
        trans
          (sym (selectedDensityPotentialIsRegularE weld scale background))
          (R108.densityPotentialIsLocalizedCompositeSum
            localized scale volume background)
  }

regularERealizationUsesExactR108Localization :
  ∀ {trajectory split inputs projection localized}
    (weld : R108RegularESemanticWeld
      {trajectory = trajectory} {split = split} {inputs = inputs}
      projection localized) →
  R222.components (asPreferredRegularERealization weld)
  ≡ R108.components localized
regularERealizationUsesExactR108Localization weld = Agda.Builtin.Equality.refl

r108ToPreferredRegularERealizationCompilerLevel : ProofLevel
r108ToPreferredRegularERealizationCompilerLevel = machineChecked

-- Least-privilege physical same-object seam after R108 localization exists:
-- identify the PRE-EXISTING density potential with evaluation of the source
-- regular-E coordinate.  Do not choose the density interpretation after seeing
-- the target.
literalR108DensityPotentialIsCMP119RegularELevel : ProofLevel
literalR108DensityPotentialIsCMP119RegularELevel = conditional
