{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBetaDrivenDensityToCMP109116CarrierRound108Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Flow
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius

record BetaDrivenLocalizedEffectiveActionFamily
    {trajectory split}
    (inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}) : Set₁ where
  field
    Volume Background Tangent Component : Set
    potentialOfDensity : Flow.Density inputs → Background → ℝ
    components : Nat → Volume → List Component
    physicalLocalizedActivity : Nat → Volume → Component → Background → ℝ

    densityPotentialIsLocalizedCompositeSum :
      ∀ scale volume background →
      potentialOfDensity (Flow.densityAt inputs scale) background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (physicalLocalizedActivity scale volume)
            (components scale volume))
          background

    commonRadius : Radius.CMP116CommonAnalyticRadius Nat Volume

open BetaDrivenLocalizedEffectiveActionFamily public

asCMP109116Continuation :
  ∀ {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}} →
  BetaDrivenLocalizedEffectiveActionFamily inputs →
  Continue.CMP109116LiteralEffectiveActionContinuation
asCMP109116Continuation {inputs = inputs} dataSet = record
  { Continue.CMP109116LiteralEffectiveActionContinuation.Scale = Nat
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Volume = Volume dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Background = Background dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Tangent = Tangent dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Component = Component dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.components = components dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      physicalLocalizedActivity dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      λ scale → potentialOfDensity dataSet (Flow.densityAt inputs scale)
  ; Continue.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      densityPotentialIsLocalizedCompositeSum dataSet
  }

cmp109PotentialIsLiteralBetaDrivenDensityPotential :
  ∀ {trajectory split}
    {inputs : Flow.BetaDrivenCompleteDensityInputs {trajectory} {split}}
    (dataSet : BetaDrivenLocalizedEffectiveActionFamily inputs)
    scale volume background →
  Continue.cmp109EffectivePotential
    (asCMP109116Continuation dataSet) scale volume background
  ≡ potentialOfDensity dataSet (Flow.densityAt inputs scale) background
cmp109PotentialIsLiteralBetaDrivenDensityPotential dataSet scale volume background = refl

round108BetaDrivenCMP109116ContinuationLevel : ProofLevel
round108BetaDrivenCMP109116ContinuationLevel = machineChecked

literalBetaDrivenCMP116LocalizationAndRadiusRound108Level : ProofLevel
literalBetaDrivenCMP116LocalizationAndRadiusRound108Level = conditional
