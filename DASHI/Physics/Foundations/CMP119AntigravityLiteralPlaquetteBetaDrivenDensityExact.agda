{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteBetaDrivenDensityExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109FiniteHistoryExact as LiteralHistory
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact as Terminal
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- LITERAL PLAQUETTE HISTORY -> BETA-DRIVEN CMP122 DENSITY INPUTS
--
-- The betaHistory field consumed by CMP122 is constructed directly from the
-- literal plaquette split and terminal inverse-square history.  No independent
-- split, coupling trajectory, or beta-history value is accepted here.
------------------------------------------------------------------------

record LiteralPlaquetteBetaDrivenDensity
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (literalHistory :
      LiteralHistory.LiteralPlaquetteCMP109FiniteHistory dataSet trajectory)
    (terminal :
      Terminal.LiteralPlaquetteTerminalHistory
        dataSet trajectory literalHistory) : Set₂ where
  field
    Density : Set
    densityAt : Nat → Density
    InSection2DensityClass : Nat → Density → Set
    Section2ConditionsAndBounds : Nat → Density → Set

    sourceScaleActive :
      ∀ scale →
      History.ActiveScale
        (Terminal.asBetaSplitInverseSquareTerminalHistory terminal)
        scale

open LiteralPlaquetteBetaDrivenDensity public

asBetaDrivenCompleteDensityInputs :
  ∀ {dataSet trajectory literalHistory terminal} →
  LiteralPlaquetteBetaDrivenDensity
    dataSet trajectory literalHistory terminal →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = trajectory}
    {split = Terminal.compiledSplit literalHistory}
asBetaDrivenCompleteDensityInputs {terminal = terminal} source = record
  { Beta.BetaDrivenCompleteDensityInputs.Density =
      Density source
  ; Beta.BetaDrivenCompleteDensityInputs.betaHistory =
      Terminal.asBetaSplitInverseSquareTerminalHistory terminal
  ; Beta.BetaDrivenCompleteDensityInputs.densityAt =
      densityAt source
  ; Beta.BetaDrivenCompleteDensityInputs.InSection2DensityClass =
      InSection2DensityClass source
  ; Beta.BetaDrivenCompleteDensityInputs.Section2ConditionsAndBounds =
      Section2ConditionsAndBounds source
  ; Beta.BetaDrivenCompleteDensityInputs.sourceScaleActive =
      sourceScaleActive source
  }

literalPlaquetteBetaDrivenDensityCompilerLevel : ProofLevel
literalPlaquetteBetaDrivenDensityCompilerLevel = machineChecked

parallelBetaHistoryArgumentRequired : Bool
parallelBetaHistoryArgumentRequired = false
