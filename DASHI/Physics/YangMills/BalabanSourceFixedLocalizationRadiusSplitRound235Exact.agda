{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceFixedLocalizationRadiusSplitRound235Exact where

------------------------------------------------------------------------
-- ROUND235 / SOURCE-FIXED LOCALIZATION != COMMON-RADIUS REALIZATION
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanSourceFixedR108EffectiveActionFamilyRound213Exact as R213

record SourceFixedCMP116Localization
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (semantics : R213.FixedR108EffectiveDensitySemantics inputs) : Set₁ where
  field
    Volume Tangent Component : Set

    components : Nat → Volume → List Component
    physicalLocalizedActivity :
      Nat → Volume → Component → R213.Background semantics → ℝ

    sourceDensityPotentialIsLocalizedCompositeSum :
      ∀ scale volume background →
      R213.interpretDensity semantics (Flow.densityAt inputs scale) background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (physicalLocalizedActivity scale volume)
            (components scale volume))
          background

open SourceFixedCMP116Localization public

withCommonRadius :
  ∀ {trajectory split inputs semantics}
    (localization : SourceFixedCMP116Localization
      {trajectory = trajectory} {split = split} {inputs = inputs} semantics) →
  Common.CMP116CommonAnalyticRadius Nat (Volume localization) →
  R213.SourceFixedR108LocalizedFamily semantics
withCommonRadius localization radius = record
  { R213.SourceFixedR108LocalizedFamily.Volume = Volume localization
  ; R213.SourceFixedR108LocalizedFamily.Tangent = Tangent localization
  ; R213.SourceFixedR108LocalizedFamily.Component = Component localization
  ; R213.SourceFixedR108LocalizedFamily.components = components localization
  ; R213.SourceFixedR108LocalizedFamily.physicalLocalizedActivity =
      physicalLocalizedActivity localization
  ; R213.SourceFixedR108LocalizedFamily.sourceDensityPotentialIsLocalizedCompositeSum =
      sourceDensityPotentialIsLocalizedCompositeSum localization
  ; R213.SourceFixedR108LocalizedFamily.commonRadius = radius
  }

sourceFixedLocalizationRadiusCompositionLevel : ProofLevel
sourceFixedLocalizationRadiusCompositionLevel = machineChecked

-- Independent physical/source realization coordinates after the split.
literalSourceFixedCMP116LocalizationLevel : ProofLevel
literalSourceFixedCMP116LocalizationLevel = conditional

literalUniformCMP116CommonRadiusLevel : ProofLevel
literalUniformCMP116CommonRadiusLevel =
  Common.literalCMP116UniformCommonRadiusInstantiationLevel
