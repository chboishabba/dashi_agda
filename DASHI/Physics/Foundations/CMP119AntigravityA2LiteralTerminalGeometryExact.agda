{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityA2LiteralTerminalGeometryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base using (1ℚ; Positive; _*_; _≤_)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact as Literal
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowACouplingBoundGeometryExact as Geometry
import DASHI.Physics.Foundations.CMP119AntigravityA2LiteralCouplingCoordinateExact as A2Literal
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- A2/LITERAL SAME-OBJECT COORDINATE -> TERMINAL ROW-A GEOMETRY
--
-- After the early coupling weld, the terminal Row-A cap is generated from
-- A2's existing finite-prefix bound.  The caller supplies only that the selected
-- terminal scale belongs to the A2 prefix.  No independent terminal
-- coupling-cap or inverse-threshold inequality remains.
------------------------------------------------------------------------

record A2LiteralTerminalGeometry
    {HistoryCarrier Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    (plaquette : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence plaquette)
    (source :
      CanonicalHistory.CanonicalLiteralPlaquetteHistory plaquette coherence)
    (coordinate : A2Literal.A2LiteralCouplingCoordinate present plaquette) : Set₁ where
  field
    terminalScale : Nat
    terminalInsideA2Prefix : terminalScale ℕ.< cutoff

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    couplingPositive : ∀ scale →
      Positive (Literal.literalCouplingAt plaquette scale)

    inverseCouplingRepresentation : ∀ scale →
      Flow.inverseCoupling
        (CanonicalHistory.trajectory coherence) scale
      * Order.square (Literal.literalCouplingAt plaquette scale)
      ≡ 1ℚ

open A2LiteralTerminalGeometry public

asCanonicalRowACouplingBoundGeometry :
  ∀ {HistoryCarrier Cell cutoff present plaquette coherence source coordinate} →
  A2LiteralTerminalGeometry
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present plaquette coherence source coordinate →
  Geometry.CanonicalRowACouplingBoundGeometry
    plaquette coherence source
    (Unified.rowAConstantsFromA2 present)
asCanonicalRowACouplingBoundGeometry
    {present = present} {coordinate = coordinate} geometry = record
  { Geometry.CanonicalRowACouplingBoundGeometry.terminalScale =
      terminalScale geometry
  ; Geometry.CanonicalRowACouplingBoundGeometry.ActiveScale =
      ActiveScale geometry
  ; Geometry.CanonicalRowACouplingBoundGeometry.terminalActive =
      terminalActive geometry
  ; Geometry.CanonicalRowACouplingBoundGeometry.gapToTerminal =
      gapToTerminal geometry
  ; Geometry.CanonicalRowACouplingBoundGeometry.scaleReachesTerminal =
      scaleReachesTerminal geometry
  ; Geometry.CanonicalRowACouplingBoundGeometry.couplingPositive =
      couplingPositive geometry
  ; Geometry.CanonicalRowACouplingBoundGeometry.terminalCouplingBelowCanonicalGamma =
      A2Literal.literalCouplingBelowCanonicalRowA
        coordinate
        (terminalScale geometry)
        (terminalInsideA2Prefix geometry)
  ; Geometry.CanonicalRowACouplingBoundGeometry.inverseCouplingRepresentation =
      inverseCouplingRepresentation geometry
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

a2LiteralTerminalGeometryCompilerLevel : ProofLevel
a2LiteralTerminalGeometryCompilerLevel = machineChecked
