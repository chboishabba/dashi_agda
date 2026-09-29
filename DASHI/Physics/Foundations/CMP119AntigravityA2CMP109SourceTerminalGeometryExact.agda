{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceTerminalGeometryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ

import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceCouplingCoordinateExact as SourceCoupling
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceRowATerminalHistoryExact as Terminal
import DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceCouplingExact as A2Source
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- A2/CMP109 COUPLING WELD -> SOURCE-OWNED TERMINAL GEOMETRY
------------------------------------------------------------------------

record A2CMP109SourceTerminalGeometry
    {HistoryCarrier Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {weld}
    (finiteHistory : FiniteHistory.CMP109PlaquetteFiniteHistory trajectory weld)
    (sourceCoupling : SourceCoupling.CMP109SourceCouplingCoordinate trajectory)
    (coordinate : A2Source.A2CMP109SourceCouplingCoordinate present sourceCoupling)
    : Set₁ where
  field
    terminalScale : Nat
    terminalInsideA2Prefix : terminalScale ℕ.< cutoff

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

open A2CMP109SourceTerminalGeometry public

asCMP109SourceRowATerminalGeometry :
  ∀ {HistoryCarrier Cell cutoff present trajectory weld finiteHistory sourceCoupling coordinate} →
  A2CMP109SourceTerminalGeometry
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present finiteHistory sourceCoupling coordinate →
  Terminal.CMP109SourceRowATerminalGeometry
    finiteHistory sourceCoupling
    (Unified.rowAConstantsFromA2 present)
asCMP109SourceRowATerminalGeometry
    {coordinate = coordinate} geometry = record
  { Terminal.CMP109SourceRowATerminalGeometry.terminalScale =
      terminalScale geometry
  ; Terminal.CMP109SourceRowATerminalGeometry.ActiveScale =
      ActiveScale geometry
  ; Terminal.CMP109SourceRowATerminalGeometry.terminalActive =
      terminalActive geometry
  ; Terminal.CMP109SourceRowATerminalGeometry.gapToTerminal =
      gapToTerminal geometry
  ; Terminal.CMP109SourceRowATerminalGeometry.scaleReachesTerminal =
      scaleReachesTerminal geometry
  ; Terminal.CMP109SourceRowATerminalGeometry.terminalCouplingBelowCanonicalGamma =
      A2Source.sourceCouplingBelowCanonicalRowA
        coordinate
        (terminalScale geometry)
        (terminalInsideA2Prefix geometry)
  }

freeTerminalCouplingCapRequired : Bool
freeTerminalCouplingCapRequired = false

freeTerminalInverseThresholdRequired : Bool
freeTerminalInverseThresholdRequired = false

freeTerminalCouplingCapRequiredIsFalse :
  freeTerminalCouplingCapRequired ≡ false
freeTerminalCouplingCapRequiredIsFalse = refl

freeTerminalInverseThresholdRequiredIsFalse :
  freeTerminalInverseThresholdRequired ≡ false
freeTerminalInverseThresholdRequiredIsFalse = refl

a2CMP109SourceTerminalGeometryCompilerLevel : ProofLevel
a2CMP109SourceTerminalGeometryCompilerLevel = machineChecked
