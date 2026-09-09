{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceFixedRegularESemanticsRound234Exact where

------------------------------------------------------------------------
-- ROUND234 / SOURCE-FIX DENSITY SEMANTICS BEFORE THE REGULAR-E WELD
--
-- R233 reuses R108 localization, but R108 alone permits a freely chosen
-- density-potential interpretation.  R213 already fixes that semantic map before
-- any BC1 target exists.  This module composes the two corrections.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource
import DASHI.Physics.YangMills.BalabanSourceFixedR108EffectiveActionFamilyRound213Exact as R213
import DASHI.Physics.YangMills.BalabanR108ToRegularERealizationRound233Exact as R233

record SourceFixedRegularESemanticWeld
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (projection : ESource.CMP119RegularESourceProjection inputs)
    (semantics : R213.FixedR108EffectiveDensitySemantics inputs)
    (localized : R213.SourceFixedR108LocalizedFamily semantics) : Set₁ where
  field
    evaluateRegularE :
      ESource.RegularTerm projection → R213.Background semantics → ℝ

    sourceDensitySemanticsIsRegularE : ∀ scale background →
      R213.interpretDensity semantics (Flow.densityAt inputs scale) background
      ≡ evaluateRegularE (ESource.selectedRegularE projection scale) background

open SourceFixedRegularESemanticWeld public

asR233SemanticWeld :
  ∀ {trajectory split inputs projection semantics localized} →
  SourceFixedRegularESemanticWeld
    {trajectory = trajectory} {split = split} {inputs = inputs}
    projection semantics localized →
  R233.R108RegularESemanticWeld
    projection (R213.asR108LocalizedEffectiveActionFamily localized)
asR233SemanticWeld weld = record
  { R233.R108RegularESemanticWeld.evaluateRegularE = evaluateRegularE weld
  ; R233.R108RegularESemanticWeld.selectedDensityPotentialIsRegularE =
      sourceDensitySemanticsIsRegularE weld
  }

sourceFixedPreferredRegularERealization :
  ∀ {trajectory split inputs projection semantics localized} →
  SourceFixedRegularESemanticWeld
    {trajectory = trajectory} {split = split} {inputs = inputs}
    projection semantics localized →
  DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredContinuationRound222Exact.PreferredRegularERealization projection
sourceFixedPreferredRegularERealization weld =
  R233.asPreferredRegularERealization (asR233SemanticWeld weld)

sourceFixedR108ToRegularECompilerLevel : ProofLevel
sourceFixedR108ToRegularECompilerLevel = machineChecked

-- Surviving physical source semantic weld after the density semantics and
-- localization family have been fixed independently of BC1.
literalSourceDensitySemanticsIsCMP119RegularELevel : ProofLevel
literalSourceDensitySemanticsIsCMP119RegularELevel = conditional

-- Existing independent source leaves reused here.
literalCMP122EffectiveDensitySemanticsLevel : ProofLevel
literalCMP122EffectiveDensitySemanticsLevel = R213.literalCMP122EffectiveDensitySemanticsLevel

literalSourceFixedCMP116LocalizationAndRadiusLevel : ProofLevel
literalSourceFixedCMP116LocalizationAndRadiusLevel =
  R213.literalSourceFixedCMP116LocalizationAndRadiusLevel
