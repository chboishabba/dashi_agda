{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceRowATerminalHistoryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (_≤_)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceCouplingCoordinateExact as SourceCoupling
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowAInverseThresholdExact as Threshold
import DASHI.Physics.Foundations.CMP119AntigravityCouplingCapToInverseThresholdExact as Converse
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SOURCE-OWNED COUPLING -> CANONICAL ROW-A TERMINAL HISTORY
--
-- Unlike the earlier plaquette terminal adapter, this module never reads a
-- coupling from the coefficient/remainder producer.  The exact CMP109 source
-- coupling coordinate supplies positivity and u_k g_k^2 = 1 directly.
------------------------------------------------------------------------

record CMP109SourceRowATerminalGeometry
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {weld}
    (finiteHistory : FiniteHistory.CMP109PlaquetteFiniteHistory trajectory weld)
    (sourceCoupling : SourceCoupling.CMP109SourceCouplingCoordinate trajectory)
    (rowA : RowA.FiniteQuarticResponseConstants) : Set₁ where
  field
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    terminalCouplingBelowCanonicalGamma :
      SourceCoupling.sourceCoupling sourceCoupling terminalScale
      ≤ RowA.canonicalQuarticResponseGamma rowA

open CMP109SourceRowATerminalGeometry public

orderDataAt :
  ∀ {trajectory weld finiteHistory sourceCoupling rowA} →
  CMP109SourceRowATerminalGeometry
    finiteHistory sourceCoupling rowA →
  Nat →
  Order.RationalInverseSquareOrderData
orderDataAt
    {trajectory = trajectory}
    {sourceCoupling = sourceCoupling}
    {rowA = rowA}
    geometry scale = record
  { Order.RationalInverseSquareOrderData.coupling =
      SourceCoupling.sourceCoupling sourceCoupling scale
  ; Order.RationalInverseSquareOrderData.thresholdCoupling =
      RowA.canonicalQuarticResponseGamma rowA
  ; Order.RationalInverseSquareOrderData.inverseCoupling =
      Flow.inverseCoupling trajectory scale
  ; Order.RationalInverseSquareOrderData.inverseThreshold =
      Threshold.canonicalInverseThreshold rowA
  ; Order.RationalInverseSquareOrderData.couplingPositive =
      SourceCoupling.sourceCouplingPositive sourceCoupling scale
  ; Order.RationalInverseSquareOrderData.thresholdCouplingPositive =
      ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)
  ; Order.RationalInverseSquareOrderData.inverseCouplingTimesSquare =
      SourceCoupling.sourceInverseSquareMeaning sourceCoupling scale
  ; Order.RationalInverseSquareOrderData.inverseThresholdTimesSquare =
      Threshold.canonicalInverseThresholdRepresentation rowA
  }

terminalInverseThreshold :
  ∀ {trajectory weld finiteHistory sourceCoupling rowA}
    (geometry :
      CMP109SourceRowATerminalGeometry
        finiteHistory sourceCoupling rowA) →
  Threshold.canonicalInverseThreshold rowA
  ≤ Flow.inverseCoupling trajectory (terminalScale geometry)
terminalInverseThreshold geometry =
  Converse.smallCouplingImpliesInverseThreshold
    (orderDataAt geometry (terminalScale geometry))
    (terminalCouplingBelowCanonicalGamma geometry)

asBetaSplitInverseSquareTerminalHistory :
  ∀ {trajectory weld finiteHistory sourceCoupling rowA} →
  CMP109SourceRowATerminalGeometry
    finiteHistory sourceCoupling rowA →
  History.BetaSplitInverseSquareTerminalHistoryData
    trajectory
    (FiniteHistory.repositoryBetaSplit finiteHistory)
asBetaSplitInverseSquareTerminalHistory
    {sourceCoupling = sourceCoupling} {rowA = rowA}
    geometry = record
  { History.BetaSplitInverseSquareTerminalHistoryData.couplingAt =
      SourceCoupling.sourceCoupling sourceCoupling
  ; History.BetaSplitInverseSquareTerminalHistoryData.gamma =
      RowA.canonicalQuarticResponseGamma rowA
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseThreshold =
      Threshold.canonicalInverseThreshold rowA
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalScale =
      terminalScale geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.ActiveScale =
      ActiveScale geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalActive =
      terminalActive geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.gapToTerminal =
      gapToTerminal geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.scaleReachesTerminal =
      scaleReachesTerminal geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.terminalInverseThreshold =
      terminalInverseThreshold geometry
  ; History.BetaSplitInverseSquareTerminalHistoryData.couplingPositive =
      SourceCoupling.sourceCouplingPositive sourceCoupling
  ; History.BetaSplitInverseSquareTerminalHistoryData.gammaPositive =
      ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseCouplingRepresentation =
      SourceCoupling.sourceInverseSquareMeaning sourceCoupling
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseThresholdRepresentation =
      Threshold.canonicalInverseThresholdRepresentation rowA
  }

coefficientSideCouplingNeededForTerminalHistory : Bool
coefficientSideCouplingNeededForTerminalHistory = false

freeTerminalInverseThresholdNeeded : Bool
freeTerminalInverseThresholdNeeded = false

coefficientSideCouplingNeededForTerminalHistoryIsFalse :
  coefficientSideCouplingNeededForTerminalHistory ≡ false
coefficientSideCouplingNeededForTerminalHistoryIsFalse = refl

freeTerminalInverseThresholdNeededIsFalse :
  freeTerminalInverseThresholdNeeded ≡ false
freeTerminalInverseThresholdNeededIsFalse = refl

cmp109SourceRowATerminalCompilerLevel : ProofLevel
cmp109SourceRowATerminalCompilerLevel = machineChecked
