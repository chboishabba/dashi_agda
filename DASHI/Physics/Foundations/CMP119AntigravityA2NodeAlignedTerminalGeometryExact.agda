{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityA2NodeAlignedTerminalGeometryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteNodeCouplingExact as Node
import DASHI.Physics.Foundations.CMP119AntigravityNodeAlignedCanonicalRowATerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityA2NodeCouplingCoordinateExact as A2Node
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- A2 NODE COUPLING -> CORRECTED TERMINAL ROW-A GEOMETRY
------------------------------------------------------------------------

record A2NodeAlignedTerminalGeometry
    {HistoryCarrier Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    {dataSet}
    (coherence : Source.LiteralPlaquetteUVChainCoherence dataSet)
    (literalSource :
      CanonicalHistory.CanonicalLiteralPlaquetteHistory dataSet coherence)
    (nodeCoupling : Node.LiteralPlaquetteNodeCoupling dataSet coherence)
    (coordinate : A2Node.A2NodeCouplingCoordinate present nodeCoupling) : Set₁ where
  field
    terminalScale : Nat
    terminalInsideA2Prefix : terminalScale ℕ.< cutoff

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

open A2NodeAlignedTerminalGeometry public

asNodeAlignedRowATerminalGeometry :
  ∀ {HistoryCarrier Cell cutoff present dataSet coherence literalSource nodeCoupling coordinate} →
  A2NodeAlignedTerminalGeometry
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present coherence literalSource nodeCoupling coordinate →
  Terminal.NodeAlignedRowATerminalGeometry
    coherence literalSource nodeCoupling
    (Unified.rowAConstantsFromA2 present)
asNodeAlignedRowATerminalGeometry
    {present = present} {coordinate = coordinate}
    geometry = record
  { Terminal.NodeAlignedRowATerminalGeometry.terminalScale =
      terminalScale geometry
  ; Terminal.NodeAlignedRowATerminalGeometry.ActiveScale =
      ActiveScale geometry
  ; Terminal.NodeAlignedRowATerminalGeometry.terminalActive =
      terminalActive geometry
  ; Terminal.NodeAlignedRowATerminalGeometry.gapToTerminal =
      gapToTerminal geometry
  ; Terminal.NodeAlignedRowATerminalGeometry.scaleReachesTerminal =
      scaleReachesTerminal geometry
  ; Terminal.NodeAlignedRowATerminalGeometry.terminalCouplingBelowCanonicalGamma =
      A2Node.sourceNodeCouplingBelowCanonicalRowA
        coordinate
        (terminalScale geometry)
        (terminalInsideA2Prefix geometry)
  }

freeTerminalCouplingCapRequired : Bool
freeTerminalCouplingCapRequired = false

freeTerminalInverseSquareRepresentationRequired : Bool
freeTerminalInverseSquareRepresentationRequired = false

freeTerminalCouplingCapRequiredIsFalse :
  freeTerminalCouplingCapRequired ≡ false
freeTerminalCouplingCapRequiredIsFalse = refl

freeTerminalInverseSquareRepresentationRequiredIsFalse :
  freeTerminalInverseSquareRepresentationRequired ≡ false
freeTerminalInverseSquareRepresentationRequiredIsFalse = refl

a2NodeAlignedTerminalGeometryCompilerLevel : ProofLevel
a2NodeAlignedTerminalGeometryCompilerLevel = machineChecked
