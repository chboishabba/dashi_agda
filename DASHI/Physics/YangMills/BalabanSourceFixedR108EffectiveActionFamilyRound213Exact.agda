{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceFixedR108EffectiveActionFamilyRound213Exact where

------------------------------------------------------------------------
-- ROUND213 / FIX THE DENSITY SEMANTICS BEFORE BUILDING THE R108 FAMILY
--
-- Round145 exposed a real degeneracy in the older density/action weld: if the
-- density -> effective-potential interpretation is chosen inside the same record
-- that is asked to prove equality with BC1, one may choose the BC1 target itself
-- and obtain a vacuous `refl`.
--
-- Round212 removes the later R108 -> BC1 post-hoc equality by constructing BC1
-- from `R108.asCMP109116Continuation`.  That is only source-safe if R108's own
-- `potentialOfDensity` has already been fixed independently of BC1.
--
-- This module enforces exactly that order:
--
--   physical/source density semantics
--       -> source-fixed localized R108 family
--       -> R108 continuation
--       -> R108-backed BC1 constructor.
--
-- The compiler below never chooses a density interpretation after seeing a BC1
-- target.  The remaining physical work is to instantiate the source semantics
-- and the literal CMP116 localization/radius data for that SAME semantics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact as R108
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

------------------------------------------------------------------------
-- SOURCE-FIXED SEMANTICS
------------------------------------------------------------------------

record FixedR108EffectiveDensitySemantics
    {trajectory split}
    (inputs : Flow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₁ where
  field
    Background : Set
    interpretDensity : Flow.Density inputs → Background → ℝ

open FixedR108EffectiveDensitySemantics public

------------------------------------------------------------------------
-- LOCALIZED FAMILY WITH NO FREELY CHOSEN `potentialOfDensity`
------------------------------------------------------------------------

record SourceFixedR108LocalizedFamily
    {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    (semantics : FixedR108EffectiveDensitySemantics inputs) : Set₁ where
  field
    Volume Tangent Component : Set

    components : Nat → Volume → List Component
    physicalLocalizedActivity :
      Nat → Volume → Component → Background semantics → ℝ

    sourceDensityPotentialIsLocalizedCompositeSum :
      ∀ scale volume background →
      interpretDensity semantics (Flow.densityAt inputs scale) background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (physicalLocalizedActivity scale volume)
            (components scale volume))
          background

    commonRadius : Radius.CMP116CommonAnalyticRadius Nat Volume

open SourceFixedR108LocalizedFamily public

asR108LocalizedEffectiveActionFamily :
  ∀ {trajectory split inputs semantics} →
  SourceFixedR108LocalizedFamily
    {trajectory = trajectory} {split = split} {inputs = inputs} semantics →
  R108.BetaDrivenLocalizedEffectiveActionFamily inputs
asR108LocalizedEffectiveActionFamily {semantics = semantics} dataSet = record
  { R108.BetaDrivenLocalizedEffectiveActionFamily.Volume = Volume dataSet
  ; R108.BetaDrivenLocalizedEffectiveActionFamily.Background = Background semantics
  ; R108.BetaDrivenLocalizedEffectiveActionFamily.Tangent = Tangent dataSet
  ; R108.BetaDrivenLocalizedEffectiveActionFamily.Component = Component dataSet
  ; R108.BetaDrivenLocalizedEffectiveActionFamily.potentialOfDensity =
      interpretDensity semantics
  ; R108.BetaDrivenLocalizedEffectiveActionFamily.components = components dataSet
  ; R108.BetaDrivenLocalizedEffectiveActionFamily.physicalLocalizedActivity =
      physicalLocalizedActivity dataSet
  ; R108.BetaDrivenLocalizedEffectiveActionFamily.densityPotentialIsLocalizedCompositeSum =
      sourceDensityPotentialIsLocalizedCompositeSum dataSet
  ; R108.BetaDrivenLocalizedEffectiveActionFamily.commonRadius = commonRadius dataSet
  }

r108PotentialIsFixedSourceSemantics :
  ∀ {trajectory split inputs semantics}
    (dataSet : SourceFixedR108LocalizedFamily
      {trajectory = trajectory} {split = split} {inputs = inputs} semantics) →
  ∀ density background →
  R108.potentialOfDensity (asR108LocalizedEffectiveActionFamily dataSet)
      density background
  ≡ interpretDensity semantics density background
r108PotentialIsFixedSourceSemantics dataSet density background = refl

r108SelectedScalePotentialIsFixedSourceSemantics :
  ∀ {trajectory split inputs semantics}
    (dataSet : SourceFixedR108LocalizedFamily
      {trajectory = trajectory} {split = split} {inputs = inputs} semantics) →
  ∀ scale background →
  R108.potentialOfDensity (asR108LocalizedEffectiveActionFamily dataSet)
      (Flow.densityAt inputs scale) background
  ≡ interpretDensity semantics (Flow.densityAt inputs scale) background
r108SelectedScalePotentialIsFixedSourceSemantics dataSet scale background = refl

r108ContinuationPotentialIsFixedSourceSemantics :
  ∀ {trajectory split inputs semantics}
    (dataSet : SourceFixedR108LocalizedFamily
      {trajectory = trajectory} {split = split} {inputs = inputs} semantics) →
  ∀ scale volume background →
  Source.cmp109EffectivePotential
      (R108.asCMP109116Continuation
        (asR108LocalizedEffectiveActionFamily dataSet))
      scale volume background
  ≡ interpretDensity semantics (Flow.densityAt inputs scale) background
r108ContinuationPotentialIsFixedSourceSemantics dataSet scale volume background = refl

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
------------------------------------------------------------------------

sourceFixedR108FamilyCompilerLevel : ProofLevel
sourceFixedR108FamilyCompilerLevel = machineChecked

sourceFixedR108ContinuationSameObjectLevel : ProofLevel
sourceFixedR108ContinuationSameObjectLevel = machineChecked

-- Physical/source leaves.  `FixedR108EffectiveDensitySemantics` must be the
-- literal CMP122 density meaning, and the localized activities/radius must be
-- extracted from the published CMP116/Sect.-2 family rather than selected to
-- fit a downstream BC1 target.
literalCMP122EffectiveDensitySemanticsLevel : ProofLevel
literalCMP122EffectiveDensitySemanticsLevel = conditional

literalSourceFixedCMP116LocalizationAndRadiusLevel : ProofLevel
literalSourceFixedCMP116LocalizationAndRadiusLevel =
  R108.literalBetaDrivenCMP116LocalizationAndRadiusRound108Level
