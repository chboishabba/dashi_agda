{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCMP109RowATerminalHistoryExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; Positive; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityCMP109PlaquetteFiniteHistoryExact as FiniteHistory
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PREFERRED SOURCE-BUILT TERMINAL HISTORY
--
-- The source trajectory is primary.  The plaquette running data is constructed
-- from it, and the beta split is compiled from the literal coefficient family.
--
-- gamma := canonical Row-A gamma
-- u_*   := 1 / gamma^2
--
-- by construction.  Thus the only terminal physics is:
--
--   * literal plaquette coupling is positive;
--   * u_k * g_k^2 = 1 on the same source trajectory;
--   * u_* <= u_terminal;
--   * finite active-scale reachability.
------------------------------------------------------------------------

gammaSquare :
  RowA.FiniteQuarticResponseConstants → ℚ
gammaSquare rowA =
  Order.square (RowA.canonicalQuarticResponseGamma rowA)

gammaSquarePositive :
  (rowA : RowA.FiniteQuarticResponseConstants) →
  0ℚ < gammaSquare rowA
gammaSquarePositive rowA =
  let
    gamma = RowA.canonicalQuarticResponseGamma rowA
    instance gammaPos : Positive gamma
    gammaPos = ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)
  in
  ℚP.positive⁻¹ (gamma * gamma)

inverseThreshold :
  RowA.FiniteQuarticResponseConstants → ℚ
inverseThreshold rowA =
  Quot.positiveReciprocal
    (gammaSquare rowA)
    (gammaSquarePositive rowA)

inverseThresholdRepresentation :
  (rowA : RowA.FiniteQuarticResponseConstants) →
  inverseThreshold rowA * gammaSquare rowA ≡ 1ℚ
inverseThresholdRepresentation rowA =
  trans
    (ℚP.*-comm (inverseThreshold rowA) (gammaSquare rowA))
    (Quot.positiveReciprocalRightInverse
      (gammaSquare rowA)
      (gammaSquarePositive rowA))

literalCouplingAt :
  ∀ {trajectory}
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory) →
  Nat → ℚ
literalCouplingAt weld scale =
  Plaquette.coupling
    (Plaquette.remainder
      (Constructor.asPhysicalRunningCouplingData weld))
    scale

record CMP109RowATerminalHistory
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (weld : Constructor.CMP109LiteralPlaquetteCoefficientWeld trajectory)
    (finiteHistory : FiniteHistory.CMP109PlaquetteFiniteHistory trajectory weld)
    (rowA : RowA.FiniteQuarticResponseConstants) : Set₁ where
  field
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    terminalInverseThreshold :
      inverseThreshold rowA
      ≤ Flow.inverseCoupling trajectory terminalScale

    couplingPositive :
      ∀ scale → Positive (literalCouplingAt weld scale)

    inverseCouplingRepresentation :
      ∀ scale →
      Flow.inverseCoupling trajectory scale
        * Order.square (literalCouplingAt weld scale)
      ≡ 1ℚ

open CMP109RowATerminalHistory public

gammaPositive :
  ∀ {trajectory weld finiteHistory rowA} →
  CMP109RowATerminalHistory trajectory weld finiteHistory rowA →
  Positive (RowA.canonicalQuarticResponseGamma rowA)
gammaPositive {rowA = rowA} history =
  ℚ.positive (RowA.canonicalQuarticResponseGammaPositive rowA)

asBetaSplitInverseSquareTerminalHistory :
  ∀ {trajectory weld finiteHistory rowA} →
  CMP109RowATerminalHistory trajectory weld finiteHistory rowA →
  History.BetaSplitInverseSquareTerminalHistoryData
    trajectory
    (FiniteHistory.repositoryBetaSplit finiteHistory)
asBetaSplitInverseSquareTerminalHistory
    {weld = weld} {finiteHistory = finiteHistory} {rowA = rowA}
    history = record
  { History.BetaSplitInverseSquareTerminalHistoryData.couplingAt =
      literalCouplingAt weld
  ; History.BetaSplitInverseSquareTerminalHistoryData.gamma =
      RowA.canonicalQuarticResponseGamma rowA
  ; History.BetaSplitInverseSquareTerminalHistoryData.inverseThreshold =
      inverseThreshold rowA
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
      inverseThresholdRepresentation rowA
  }

cmp109RowATerminalHistoryCompilerLevel : ProofLevel
cmp109RowATerminalHistoryCompilerLevel = machineChecked

cmp109RowATerminalHistoryPhysicalLevel : ProofLevel
cmp109RowATerminalHistoryPhysicalLevel = conditional
