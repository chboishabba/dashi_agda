{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact where

------------------------------------------------------------------------
-- ROUND247 / CMP119 THEOREM 1 -> PREFERRED CMP109/CMP116 CONTINUATION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue

asCMP109116Continuation :
  ∀ {trajectory split history}
    {dataSet : R246.BetaDrivenRegularESection2Inputs
      {trajectory = trajectory} {split = split} history} →
  Source.Balaban1989Theorem1Witness
    (Beta.betaDrivenCompleteDensityFlow
      (R246.asBetaDrivenCompleteDensityInputs dataSet)) →
  (Tangent : Set) →
  Continue.CMP109116LiteralEffectiveActionContinuation
asCMP109116Continuation {dataSet = dataSet} theorem1 Tangent = record
  { Continue.CMP109116LiteralEffectiveActionContinuation.Scale = Nat
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Volume = R246.Volume dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Background = R246.Background dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Tangent = Tangent
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Component = R246.Component dataSet
  ; Continue.CMP109116LiteralEffectiveActionContinuation.components =
      λ scale volume → R246.components (R246.regularEFormFromTheorem1 theorem1 scale) volume
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      λ scale volume component →
        R246.localizedRegularActivity
          (R246.regularEFormFromTheorem1 theorem1 scale) volume component
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      λ scale _ → R246.regularE (R246.regularEFormFromTheorem1 theorem1 scale)
  ; Continue.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      λ scale volume →
        R246.regularEIsLocalizedCompositeSum
          (R246.regularEFormFromTheorem1 theorem1 scale) volume
  }

continuationPotentialIsTheorem1RegularE :
  ∀ {trajectory split history}
    {dataSet : R246.BetaDrivenRegularESection2Inputs
      {trajectory = trajectory} {split = split} history}
    (theorem1 : Source.Balaban1989Theorem1Witness
      (Beta.betaDrivenCompleteDensityFlow
        (R246.asBetaDrivenCompleteDensityInputs dataSet)))
    (Tangent : Set) →
  ∀ scale volume background →
  Continue.cmp109EffectivePotential
    (asCMP109116Continuation theorem1 Tangent)
    scale volume background
  ≡ R246.regularE (R246.regularEFormFromTheorem1 theorem1 scale) background
continuationPotentialIsTheorem1RegularE theorem1 Tangent scale volume background = refl

theorem1RegularEContinuationCompilerLevel : ProofLevel
theorem1RegularEContinuationCompilerLevel = machineChecked

-- The literal physical/source payment is now the Section-2 predicate binding on
-- the exact beta-driven flow.  The imported Theorem-1 authority then yields the
-- regular E_k function and its localized decomposition on every selected scale.
literalCMP119RegularESection2PredicateInstantiationLevel : ProofLevel
literalCMP119RegularESection2PredicateInstantiationLevel =
  R246.literalCMP119RegularESection2PredicateInstantiationLevel
