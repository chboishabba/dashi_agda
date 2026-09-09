{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact where

------------------------------------------------------------------------
-- ROUND246 / CONSUMER-INDEXED CMP119 SECTION-2 FORM
--
-- CMP119 Theorem 1 says the selected density satisfies all inductive assumptions.
-- For the BC1 consumer, the part of that inductive form we need is exactly:
--
--   * the regular small-field effective action E_k as a function of background;
--   * its localized representation (2.25)--(2.27).
--
-- This module makes that source meaning the literal `InSection2DensityClass`
-- predicate.  Hence a Balaban Theorem-1 witness on this flow produces E_k and
-- its localization directly, rather than requiring inversion of an abstract
-- density or construction of unrelated R/B/vacuum sectors first.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite

record CMP119RegularESection2Form
    (Density Background Volume Component : Set)
    (scale : Nat) (density : Density) : Set₁ where
  field
    regularE : Background → ℝ
    components : Volume → List Component
    localizedRegularActivity : Volume → Component → Background → ℝ

    regularEIsLocalizedCompositeSum : ∀ volume background →
      regularE background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (localizedRegularActivity volume)
            (components volume))
          background

open CMP119RegularESection2Form public

record BetaDrivenRegularESection2Inputs
    {trajectory split}
    (history : History.BetaSplitInverseSquareTerminalHistoryData trajectory split) : Set₂ where
  field
    Density Background Volume Component : Set
    densityAt : Nat → Density
    sourceScaleActive : ∀ scale → History.ActiveScale history scale

    -- Other CMP122 bounds remain a separate predicate; BC1 does not consume
    -- them merely to obtain E_k and its localized decomposition.
    Section2ConditionsAndBounds : Nat → Density → Set

open BetaDrivenRegularESection2Inputs public

asBetaDrivenCompleteDensityInputs :
  ∀ {trajectory split history} →
  BetaDrivenRegularESection2Inputs
    {trajectory = trajectory} {split = split} history →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = trajectory} {split = split}
asBetaDrivenCompleteDensityInputs {history = history} dataSet = record
  { Beta.BetaDrivenCompleteDensityInputs.Density = Density dataSet
  ; Beta.BetaDrivenCompleteDensityInputs.betaHistory = history
  ; Beta.BetaDrivenCompleteDensityInputs.densityAt = densityAt dataSet
  ; Beta.BetaDrivenCompleteDensityInputs.InSection2DensityClass =
      λ scale density →
        CMP119RegularESection2Form
          (Density dataSet) (Background dataSet) (Volume dataSet)
          (Component dataSet) scale density
  ; Beta.BetaDrivenCompleteDensityInputs.Section2ConditionsAndBounds =
      Section2ConditionsAndBounds dataSet
  ; Beta.BetaDrivenCompleteDensityInputs.sourceScaleActive = sourceScaleActive dataSet
  }

regularEFormFromTheorem1 :
  ∀ {trajectory split history}
    {dataSet : BetaDrivenRegularESection2Inputs
      {trajectory = trajectory} {split = split} history} →
  Source.Balaban1989Theorem1Witness
    (Beta.betaDrivenCompleteDensityFlow
      (asBetaDrivenCompleteDensityInputs dataSet)) →
  ∀ scale →
  CMP119RegularESection2Form
    (Density dataSet) (Background dataSet) (Volume dataSet) (Component dataSet)
    scale (densityAt dataSet scale)
regularEFormFromTheorem1 theorem1 scale =
  Source.effectiveDensitiesPreserveSection2Form theorem1 scale

regularESection2PredicateCompilerLevel : ProofLevel
regularESection2PredicateCompilerLevel = machineChecked

-- Published source authority: CMP119 Theorem 1 preserves all inductive
-- assumptions, including the regular-E representation (2.25)--(2.29).
cmp119RegularESection2TheoremSourceLevel : ProofLevel
cmp119RegularESection2TheoremSourceLevel = Source.balaban1989Theorem1SourceLevel

-- The surviving source/repository seam is to instantiate the beta-driven flow's
-- literal Section-2 predicate with this function/localization representation.
-- Once a Theorem-1 witness is supplied on that exact flow, E_k is produced.
literalCMP119RegularESection2PredicateInstantiationLevel : ProofLevel
literalCMP119RegularESection2PredicateInstantiationLevel = conditional
