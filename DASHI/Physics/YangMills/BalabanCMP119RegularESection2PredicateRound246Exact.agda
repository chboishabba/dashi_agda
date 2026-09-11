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
--
-- ARCHAEOLOGY CORRECTION (2026-09-11): the older source-shaped finite-mode
-- theorem carrier already restricts CMP122 Theorem 1 to the actually active RG
-- scales.  Keep the original all-Nat wrapper below for compatibility, but expose
-- the preferred active-scale wrapper as well.  The latter does not require a
-- fictitious proof that every Nat is an active source scale.
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
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as FiniteHistory
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as Active

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

------------------------------------------------------------------------
-- Legacy all-Nat wrapper retained for compatibility with Round247.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Preferred source-shaped active-scale wrapper.
--
-- `Balaban1989ActiveScaleTheorem1BetaBridgeExact` already records the finite
-- UV trajectory with an `ActiveScale` fibre.  We instantiate its Sect.-2 form
-- predicate with the same consumer-minimal regular-E/localization object above.
-- No conversion to the stronger all-Nat beta-driven wrapper is required.
------------------------------------------------------------------------

record ActiveRegularESection2Inputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    (betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom)
    (history : FiniteHistory.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData) : Set₂ where
  field
    Density Background Volume Component : Set
    densityAt : Nat → Density

    -- Kept distinct because CMP122 Theorem 1 also owns the quantitative Sect.-2
    -- conditions/bounds, while the BC1 extraction below consumes only the form.
    Section2ConditionsAndBounds : Nat → Density → Set

open ActiveRegularESection2Inputs public

asActiveRegularESection2Flow :
  ∀ {trajectory Mode Atom betaData history} →
  ActiveRegularESection2Inputs
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    betaData history →
  Active.ActiveEffectiveDensityFlow
    trajectory Mode Atom
    (ActiveRegularESection2Inputs.Density _)
    betaData history
asActiveRegularESection2Flow dataSet = record
  { Active.ActiveEffectiveDensityFlow.densityAt =
      ActiveRegularESection2Inputs.densityAt dataSet
  ; Active.ActiveEffectiveDensityFlow.InSection2DensityClass =
      λ scale density →
        CMP119RegularESection2Form
          (ActiveRegularESection2Inputs.Density dataSet)
          (ActiveRegularESection2Inputs.Background dataSet)
          (ActiveRegularESection2Inputs.Volume dataSet)
          (ActiveRegularESection2Inputs.Component dataSet)
          scale density
  ; Active.ActiveEffectiveDensityFlow.Section2ConditionsAndBounds =
      ActiveRegularESection2Inputs.Section2ConditionsAndBounds dataSet
  }

activeRegularEFormFromTheorem1 :
  ∀ {trajectory Mode Atom betaData history}
    {dataSet : ActiveRegularESection2Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      betaData history} →
  Active.ActiveBalaban1989Theorem1Witness
    (asActiveRegularESection2Flow dataSet) →
  ∀ scale →
  FiniteHistory.ActiveScale history scale →
  CMP119RegularESection2Form
    (ActiveRegularESection2Inputs.Density dataSet)
    (ActiveRegularESection2Inputs.Background dataSet)
    (ActiveRegularESection2Inputs.Volume dataSet)
    (ActiveRegularESection2Inputs.Component dataSet)
    scale (ActiveRegularESection2Inputs.densityAt dataSet scale)
activeRegularEFormFromTheorem1 theorem1 scale active =
  Active.effectiveDensitiesPreserveSection2Form theorem1 scale active

activeRegularESection2PredicateCompilerLevel : ProofLevel
activeRegularESection2PredicateCompilerLevel = machineChecked

activeScaleCouplingHypothesisCompilerLevel : ProofLevel
activeScaleCouplingHypothesisCompilerLevel =
  Active.activeScaleCMP122CouplingHypothesisFromFiniteBetaLevel

regularESection2PredicateCompilerLevel : ProofLevel
regularESection2PredicateCompilerLevel = machineChecked

-- Published source authority: CMP119 Theorem 1 preserves all inductive
-- assumptions, including the regular-E representation (2.25)--(2.29).
cmp119RegularESection2TheoremSourceLevel : ProofLevel
cmp119RegularESection2TheoremSourceLevel = Source.balaban1989Theorem1SourceLevel

-- The surviving source/repository seam is to instantiate the beta-driven flow's
-- literal Section-2 predicate with this function/localization representation.
-- On the preferred finite-active route this means the exact active-scale density
-- family plus the source theorem witness; no proof that every Nat is active is
-- required. Once the source witness is supplied, E_k is projected mechanically.
literalCMP119RegularESection2PredicateInstantiationLevel : ProofLevel
literalCMP119RegularESection2PredicateInstantiationLevel = conditional
