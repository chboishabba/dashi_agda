{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowALiteralTerminalHistoryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; Positive; _*_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalLiteralPlaquetteHistoryExact as CanonicalHistory
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact as Terminal
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED TERMINAL HISTORY: gamma IS THE CANONICAL ROW-A CAP
--
-- No separate history gamma and no history-gamma <= Row-A-cap proof exist on
-- this route.  The threshold coupling is definitionally the same object selected
-- by the Row-A small-coupling theorem.
------------------------------------------------------------------------

record CanonicalRowALiteralTerminalHistory
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (coherence : Source.LiteralPlaquetteUVChainCoherence dataSet)
    (source :
      CanonicalHistory.CanonicalLiteralPlaquetteHistory dataSet coherence)
    (rowA : RowA.FiniteQuarticResponseConstants) : Set₁ where
  field
    inverseThreshold : ℚ
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    terminalInverseThreshold :
      inverseThreshold ≤
      Flow.inverseCoupling
        (CanonicalHistory.trajectory coherence)
        terminalScale

    couplingPositive : ∀ scale →
      Positive (Terminal.literalCouplingAt dataSet scale)

    inverseCouplingRepresentation : ∀ scale →
      Flow.inverseCoupling
        (CanonicalHistory.trajectory coherence) scale
      * Order.square (Terminal.literalCouplingAt dataSet scale)
      ≡ 1ℚ

    inverseThresholdRepresentation :
      inverseThreshold
      * Order.square (RowA.canonicalQuarticResponseGamma rowA)
      ≡ 1ℚ

open CanonicalRowALiteralTerminalHistory public

gammaPositive :
  ∀ {dataSet coherence source rowA} →
  CanonicalRowALiteralTerminalHistory dataSet coherence source rowA →
  Positive (RowA.canonicalQuarticResponseGamma rowA)
gammaPositive {rowA = rowA} history =
  ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)

asLiteralPlaquetteTerminalHistory :
  ∀ {dataSet coherence source rowA} →
  CanonicalRowALiteralTerminalHistory dataSet coherence source rowA →
  Terminal.LiteralPlaquetteTerminalHistory
    dataSet
    (CanonicalHistory.trajectory coherence)
    (CanonicalHistory.asLiteralPlaquetteCMP109FiniteHistory source)
asLiteralPlaquetteTerminalHistory
    {dataSet = dataSet} {coherence = coherence} {source = source} {rowA = rowA}
    history = record
  { Terminal.LiteralPlaquetteTerminalHistory.gamma =
      RowA.canonicalQuarticResponseGamma rowA
  ; Terminal.LiteralPlaquetteTerminalHistory.inverseThreshold =
      inverseThreshold history
  ; Terminal.LiteralPlaquetteTerminalHistory.terminalScale =
      terminalScale history
  ; Terminal.LiteralPlaquetteTerminalHistory.ActiveScale =
      ActiveScale history
  ; Terminal.LiteralPlaquetteTerminalHistory.terminalActive =
      terminalActive history
  ; Terminal.LiteralPlaquetteTerminalHistory.gapToTerminal =
      gapToTerminal history
  ; Terminal.LiteralPlaquetteTerminalHistory.scaleReachesTerminal =
      scaleReachesTerminal history
  ; Terminal.LiteralPlaquetteTerminalHistory.terminalInverseThreshold =
      terminalInverseThreshold history
  ; Terminal.LiteralPlaquetteTerminalHistory.couplingPositive =
      couplingPositive history
  ; Terminal.LiteralPlaquetteTerminalHistory.gammaPositive =
      gammaPositive history
  ; Terminal.LiteralPlaquetteTerminalHistory.inverseCouplingRepresentation =
      inverseCouplingRepresentation history
  ; Terminal.LiteralPlaquetteTerminalHistory.inverseThresholdRepresentation =
      inverseThresholdRepresentation history
  }

historyGammaIsCanonicalRowAGamma :
  ∀ {dataSet coherence source rowA}
    (history :
      CanonicalRowALiteralTerminalHistory dataSet coherence source rowA) →
  History.gamma
    (Terminal.asBetaSplitInverseSquareTerminalHistory
      (asLiteralPlaquetteTerminalHistory history))
  ≡ RowA.canonicalQuarticResponseGamma rowA
historyGammaIsCanonicalRowAGamma history = refl

separateHistoryGammaRequired : Bool
separateHistoryGammaRequired = false

historyGammaToRowACapComparisonRequired : Bool
historyGammaToRowACapComparisonRequired = false

canonicalRowALiteralTerminalHistoryCompilerLevel : ProofLevel
canonicalRowALiteralTerminalHistoryCompilerLevel = machineChecked
