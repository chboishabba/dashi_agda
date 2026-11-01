{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; Positive; _*_; _≤_)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteCMP109FiniteHistoryExact as LiteralHistory
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- LITERAL PLAQUETTE HISTORY -> EXACT CMP122 TERMINAL HISTORY
--
-- The split is not a free argument: it is definitionally the split compiled
-- from the UV-oriented literal plaquette certificates.  The only remaining
-- representation data are the physical couplings and their inverse-square
-- identities plus the one terminal threshold.
------------------------------------------------------------------------

literalCouplingAt :
  Plaquette.PhysicalRunningCouplingData Nat →
  Nat → ℚ
literalCouplingAt dataSet scale =
  Plaquette.coupling (Plaquette.remainder dataSet) scale

record LiteralPlaquetteTerminalHistory
    (dataSet : Plaquette.PhysicalRunningCouplingData Nat)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (literalHistory :
      LiteralHistory.LiteralPlaquetteCMP109FiniteHistory dataSet trajectory) : Set₁ where
  field
    gamma inverseThreshold : ℚ
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    terminalInverseThreshold :
      inverseThreshold ≤ Flow.inverseCoupling trajectory terminalScale

    couplingPositive : ∀ scale →
      Positive (literalCouplingAt dataSet scale)
    gammaPositive : Positive gamma

    inverseCouplingRepresentation : ∀ scale →
      Flow.inverseCoupling trajectory scale
        * Order.square (literalCouplingAt dataSet scale)
      ≡ 1ℚ

    inverseThresholdRepresentation :
      inverseThreshold * Order.square gamma ≡ 1ℚ

open LiteralPlaquetteTerminalHistory public

compiledSplit :
  ∀ {dataSet trajectory}
    (literalHistory :
      LiteralHistory.LiteralPlaquetteCMP109FiniteHistory dataSet trajectory) →
  Split.FiniteLatticeBetaSplit trajectory
compiledSplit =
  LiteralHistory.literalPlaquetteGivesRepositoryBetaSplit

asBetaSplitInverseSquareTerminalHistory :
  ∀ {dataSet trajectory literalHistory} →
  LiteralPlaquetteTerminalHistory dataSet trajectory literalHistory →
  History.BetaSplitInverseSquareTerminalHistoryData
    trajectory
    (compiledSplit literalHistory)
asBetaSplitInverseSquareTerminalHistory
    {dataSet = plaquette} history = record
  { History.BetaSplitInverseSquareTerminalHistoryData.couplingAt =
      literalCouplingAt plaquette
  ; History.BetaSplitInverseSquareTerminalHistoryData.gamma =
      gamma history
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseThreshold =
      inverseThreshold history
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalScale =
      terminalScale history
  ; History.BetaSplitInverseSquareTerminalHistoryData.ActiveScale =
      ActiveScale history
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalActive =
      terminalActive history
  ; History.BetaSplitInverseSquareTerminalHistoryData.gapToTerminal =
      gapToTerminal history
  ; History.BetaSplitInverseSquareTerminalHistoryData.scaleReachesTerminal =
      scaleReachesTerminal history
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalInverseThreshold =
      terminalInverseThreshold history
  ; History.BetaSplitInverseSquareTerminalHistoryData.couplingPositive =
      couplingPositive history
  ; History.BetaSplitInverseSquareTerminalHistoryData.gammaPositive =
      gammaPositive history
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseCouplingRepresentation =
      inverseCouplingRepresentation history
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseThresholdRepresentation =
      inverseThresholdRepresentation history
  }

literalPlaquetteTerminalHistoryCompilerLevel : ProofLevel
literalPlaquetteTerminalHistoryCompilerLevel = machineChecked

-- There is no second beta split or coupling trajectory here.  Remaining source
-- inputs are exactly the physical coupling values/inverse-square identities and
-- terminal-threshold geometry on the literal plaquette trajectory.
literalPlaquetteTerminalHistorySourceLevel : ProofLevel
literalPlaquetteTerminalHistorySourceLevel = conditional
