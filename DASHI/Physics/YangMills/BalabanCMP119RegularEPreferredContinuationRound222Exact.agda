{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularEPreferredContinuationRound222Exact where

------------------------------------------------------------------------
-- ROUND222 / PREFERRED REGULAR-E -> CMP109/CMP116 CONTINUATION
--
-- Round221 isolates the least source coordinate consumed by BC1: the literal
-- CMP119 regular E_k sector of the beta-driven density.  This module gives that
-- source coordinate its pointwise meaning and CMP116 localized decomposition,
-- then constructs the exact CMP109/CMP116 continuation directly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue

record PreferredRegularERealization
    {trajectory split inputs}
    (projection : ESource.CMP119RegularESourceProjection
      {trajectory = trajectory} {split = split} inputs) : Set₁ where
  field
    Background Volume Tangent Component : Set

    evaluateRegularE : ESource.RegularTerm projection → Background → ℝ

    components : Nat → Volume → List Component
    localizedRegularActivity :
      Nat → Volume → Component → Background → ℝ

    selectedRegularEIsLocalizedCompositeSum :
      ∀ scale volume background →
      evaluateRegularE (ESource.selectedRegularE projection scale) background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (localizedRegularActivity scale volume)
            (components scale volume))
          background

open PreferredRegularERealization public

asCMP109116Continuation :
  ∀ {trajectory split inputs projection} →
  PreferredRegularERealization
    {trajectory = trajectory} {split = split} {inputs = inputs} projection →
  Continue.CMP109116LiteralEffectiveActionContinuation
asCMP109116Continuation {projection = projection} realization = record
  { Continue.CMP109116LiteralEffectiveActionContinuation.Scale = Nat
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Volume = Volume realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Background = Background realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Tangent = Tangent realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Component = Component realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.components = components realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      localizedRegularActivity realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      λ scale _ → evaluateRegularE realization
        (ESource.selectedRegularE projection scale)
  ; Continue.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      selectedRegularEIsLocalizedCompositeSum realization
  }

cmp109PotentialIsSelectedCMP119RegularE :
  ∀ {trajectory split inputs projection}
    (realization : PreferredRegularERealization
      {trajectory = trajectory} {split = split} {inputs = inputs} projection) →
  ∀ scale volume background →
  Continue.cmp109EffectivePotential (asCMP109116Continuation realization)
      scale volume background
  ≡ evaluateRegularE realization
      (ESource.selectedRegularE projection scale) background
cmp109PotentialIsSelectedCMP119RegularE realization scale volume background = refl

preferredRegularEContinuationCompilerLevel : ProofLevel
preferredRegularEContinuationCompilerLevel = machineChecked

preferredRegularEToCMP109PotentialSameObjectLevel : ProofLevel
preferredRegularEToCMP109PotentialSameObjectLevel = machineChecked

-- Physical/source realization after the source projection is known: give the
-- literal E_k pointwise meaning and its CMP116 localized activity decomposition
-- on the same background carrier.
literalPreferredRegularERealizationLevel : ProofLevel
literalPreferredRegularERealizationLevel = conditional
