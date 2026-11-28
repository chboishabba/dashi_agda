module DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger Dashen and David J. Gross,
-- "Relationship between lattice and continuum definitions of the
-- gauge-theory coupling", Physical Review D 23 (1981), 2340--2344.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Remove the last anonymous order implication from the finite small-coupling
-- history.  A caller now supplies only the literal representation equations
--
--   u_k g_k^2 = 1,
--   u_* gamma^2 = 1,
--
-- together with positivity.  The rational inverse-square theorem derives
--
--   u_* <= u_k  ->  g_k <= gamma
--
-- and the existing beta-split/terminal theorem propagates this to every
-- active RG scale.  Thus the remaining coupling-history physics is genuinely
-- the beta estimates and the identification of source u_k,g_k, not an
-- unproved order axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; Positive; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.Balaban1989BetaSplitTerminalHistoryExact as Terminal

record BetaSplitInverseSquareTerminalHistoryData
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (split : Split.FiniteLatticeBetaSplit trajectory) : Set₁ where
  field
    couplingAt : Nat → ℚ
    gamma inverseThreshold : ℚ
    terminalScale : Nat

    ActiveScale : Nat → Set
    terminalActive : ActiveScale terminalScale

    gapToTerminal : ∀ scale → ActiveScale scale → Nat
    scaleReachesTerminal : ∀ scale (active : ActiveScale scale) →
      Finite.advance scale (gapToTerminal scale active) ≡ terminalScale

    terminalInverseThreshold :
      inverseThreshold ≤ Flow.inverseCoupling trajectory terminalScale

    couplingPositive : ∀ scale → Positive (couplingAt scale)
    gammaPositive : Positive gamma

    inverseCouplingRepresentation : ∀ scale →
      Flow.inverseCoupling trajectory scale
        * Order.square (couplingAt scale)
      ≡ 1ℚ

    inverseThresholdRepresentation :
      inverseThreshold * Order.square gamma ≡ 1ℚ

open BetaSplitInverseSquareTerminalHistoryData public

orderDataAtScale :
  ∀ {trajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory} →
  BetaSplitInverseSquareTerminalHistoryData trajectory split →
  Nat → Order.RationalInverseSquareOrderData
orderDataAtScale {trajectory} dataSet scale = record
  { coupling = couplingAt dataSet scale
  ; thresholdCoupling = gamma dataSet
  ; inverseCoupling =
      Flow.inverseCoupling trajectory scale
  ; inverseThreshold =
      inverseThreshold dataSet
  ; couplingPositive =
      couplingPositive dataSet scale
  ; thresholdCouplingPositive =
      gammaPositive dataSet
  ; inverseCouplingTimesSquare =
      inverseCouplingRepresentation dataSet scale
  ; inverseThresholdTimesSquare =
      inverseThresholdRepresentation dataSet
  }

inverseThresholdImpliesSmallCouplingExact :
  ∀ {trajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (dataSet : BetaSplitInverseSquareTerminalHistoryData trajectory split)
    scale →
  inverseThreshold dataSet ≤ Flow.inverseCoupling trajectory scale →
  couplingAt dataSet scale ≤ gamma dataSet
inverseThresholdImpliesSmallCouplingExact dataSet scale =
  Order.inverseSquareThresholdImpliesSmallCoupling
    (orderDataAtScale dataSet scale)

asBetaSplitTerminalHistory :
  ∀ {trajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory} →
  BetaSplitInverseSquareTerminalHistoryData trajectory split →
  Terminal.BetaSplitTerminalHistoryData trajectory split
asBetaSplitTerminalHistory dataSet = record
  { couplingAt = couplingAt dataSet
  ; gamma = gamma dataSet
  ; inverseThreshold =
      inverseThreshold dataSet
  ; terminalScale = terminalScale dataSet
  ; ActiveScale = ActiveScale dataSet
  ; terminalActive = terminalActive dataSet
  ; gapToTerminal = gapToTerminal dataSet
  ; scaleReachesTerminal =
      scaleReachesTerminal dataSet
  ; terminalInverseThreshold =
      terminalInverseThreshold dataSet
  ; inverseThresholdImpliesSmallCoupling =
      inverseThresholdImpliesSmallCouplingExact dataSet
  }

smallCouplingAtEveryActiveScale :
  ∀ {trajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (dataSet : BetaSplitInverseSquareTerminalHistoryData trajectory split)
    scale → ActiveScale dataSet scale →
  couplingAt dataSet scale ≤ gamma dataSet
smallCouplingAtEveryActiveScale dataSet =
  Terminal.betaSplitSmallCouplingAtActiveScale
    (asBetaSplitTerminalHistory dataSet)

balabanBetaSplitInverseSquareHistoryAssemblyLevel : ProofLevel
balabanBetaSplitInverseSquareHistoryAssemblyLevel = machineChecked

balabanBetaSplitInverseSquareSmallCouplingLevel : ProofLevel
balabanBetaSplitInverseSquareSmallCouplingLevel = machineChecked
