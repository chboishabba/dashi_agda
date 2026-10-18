{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityNodeAlignedBetaDrivenDensityExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteNodeCouplingExact as Node
import DASHI.Physics.Foundations.CMP119AntigravityNodeAlignedCanonicalRowATerminalHistoryExact as Terminal
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CORRECTED NODE-ALIGNED HISTORY -> BETA-DRIVEN CMP122 DENSITY INPUTS
--
-- BetaDrivenCompleteDensityInputs receives the exact coupling history
--
--   couplingAt = Node.sourceCoupling
--
-- so every downstream CMP119/CMP122 state is on the corrected source-node
-- coordinate definitionally.
------------------------------------------------------------------------

record NodeAlignedBetaDrivenDensity
    {dataSet}
    (coherence : Source.LiteralPlaquetteUVChainCoherence dataSet)
    (literalSource :
      CanonicalHistory.CanonicalLiteralPlaquetteHistory dataSet coherence)
    (nodeCoupling : Node.LiteralPlaquetteNodeCoupling dataSet coherence)
    {rowA}
    (terminal :
      Terminal.NodeAlignedRowATerminalGeometry
        coherence literalSource nodeCoupling rowA) : Set₂ where
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

open NodeAlignedBetaDrivenDensity public

asBetaDrivenCompleteDensityInputs :
  ∀ {dataSet coherence literalSource nodeCoupling rowA terminal} →
  NodeAlignedBetaDrivenDensity
    coherence literalSource nodeCoupling terminal →
  Beta.BetaDrivenCompleteDensityInputs
    {trajectory = CanonicalHistory.trajectory coherence}
    {split = CanonicalHistory.compiledSplit literalSource}
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

betaHistoryCouplingIsNodeAlignedSourceCoupling :
  ∀ {dataSet coherence literalSource nodeCoupling rowA terminal}
    (source :
      NodeAlignedBetaDrivenDensity
        coherence literalSource nodeCoupling terminal)
    scale →
  History.couplingAt
    (Beta.betaHistory (asBetaDrivenCompleteDensityInputs source))
    scale
  ≡ Node.sourceCoupling nodeCoupling scale
betaHistoryCouplingIsNodeAlignedSourceCoupling source scale = refl

oldSameIndexProducerCouplingNeeded : Bool
oldSameIndexProducerCouplingNeeded = false

oldSameIndexProducerCouplingNeededIsFalse :
  oldSameIndexProducerCouplingNeeded ≡ false
oldSameIndexProducerCouplingNeededIsFalse = refl

nodeAlignedBetaDrivenDensityCompilerLevel : ProofLevel
nodeAlignedBetaDrivenDensityCompilerLevel = machineChecked
