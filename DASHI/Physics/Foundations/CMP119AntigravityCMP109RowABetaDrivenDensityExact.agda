{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109RowABetaDrivenDensityExact where

open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.Foundations.CMP119AntigravityCMP109RowATerminalHistoryExact as Terminal
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SOURCE-BUILT TERMINAL HISTORY -> CMP122 BETA-DRIVEN DENSITY
------------------------------------------------------------------------

record CMP109RowABetaDrivenDensity
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (finiteHistory : FiniteHistory.CMP109PlaquetteFiniteHistory trajectory weld)
    (rowA : RowA.FiniteQuarticResponseConstants)
    (terminal :
      Terminal.CMP109RowATerminalHistory trajectory weld finiteHistory rowA) : Set₂ where
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

open CMP109RowABetaDrivenDensity public

asBetaDrivenCompleteDensityInputs :
  ∀ {trajectory weld finiteHistory rowA terminal} →
  CMP109RowABetaDrivenDensity
    trajectory weld finiteHistory rowA terminal →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = trajectory}
    {split = FiniteHistory.repositoryBetaSplit finiteHistory}
asBetaDrivenCompleteDensityInputs
    {terminal = terminal} source = record
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

cmp109RowABetaDrivenDensityCompilerLevel : ProofLevel
cmp109RowABetaDrivenDensityCompilerLevel = machineChecked
