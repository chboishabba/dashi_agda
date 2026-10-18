{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceRowABetaDrivenDensityExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceCouplingCoordinateExact as SourceCoupling
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceRowATerminalHistoryExact as Terminal
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PRIMARY CMP109 SOURCE COUPLING -> CMP122 BETA-DRIVEN DENSITY
------------------------------------------------------------------------

record CMP109SourceRowABetaDrivenDensity
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {weld}
    (finiteHistory : FiniteHistory.CMP109PlaquetteFiniteHistory trajectory weld)
    (sourceCoupling : SourceCoupling.CMP109SourceCouplingCoordinate trajectory)
    (rowA : RowA.FiniteQuarticResponseConstants)
    (terminal :
      Terminal.CMP109SourceRowATerminalGeometry
        finiteHistory sourceCoupling rowA) : Set₂ where
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

open CMP109SourceRowABetaDrivenDensity public

asBetaDrivenCompleteDensityInputs :
  ∀ {trajectory weld finiteHistory sourceCoupling rowA terminal} →
  CMP109SourceRowABetaDrivenDensity
    finiteHistory sourceCoupling rowA terminal →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = trajectory}
    {split = FiniteHistory.repositoryBetaSplit finiteHistory}
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

betaHistoryCouplingIsCMP109SourceCoupling :
  ∀ {trajectory weld finiteHistory sourceCoupling rowA terminal}
    (source :
      CMP109SourceRowABetaDrivenDensity
        finiteHistory sourceCoupling rowA terminal)
    scale →
  History.couplingAt
      (Beta.betaHistory (asBetaDrivenCompleteDensityInputs source))
      scale
  ≡ SourceCoupling.sourceCoupling sourceCoupling scale
betaHistoryCouplingIsCMP109SourceCoupling source scale = refl

coefficientCouplingPromotedIntoCMP122History : Bool
coefficientCouplingPromotedIntoCMP122History = false

coefficientCouplingPromotedIntoCMP122HistoryIsFalse :
  coefficientCouplingPromotedIntoCMP122History ≡ false
coefficientCouplingPromotedIntoCMP122HistoryIsFalse = refl

cmp109SourceRowABetaDrivenDensityCompilerLevel : ProofLevel
cmp109SourceRowABetaDrivenDensityCompilerLevel = machineChecked
