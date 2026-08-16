module DASHI.Physics.YangMills.Balaban1989BetaSplitTerminalHistoryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
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
-- Feed the finite-lattice beta decomposition directly into the terminal-
-- threshold small-coupling route.  The caller no longer supplies beta>=0:
-- it is derived from the already isolated Gaussian/interacting split.
--
-- This makes the separation of tasks explicit:
--
--   betaZ >= b*, |betaInt| <= b*/2
--       -> beta>=0
--       -> inverse coupling monotone toward the coarser scale
--       -> one terminal inverse threshold controls every active UV scale
--       -> CMP122 Theorem-1 small-coupling hypothesis,
--
-- after only the elementary u=1/g^2 order dictionary is instantiated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4BetaSplitToSmallCouplingMonotonicityExact as Monotone
import DASHI.Physics.YangMills.Balaban1989TerminalInverseThresholdHistoryExact as Terminal
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite

record BetaSplitTerminalHistoryData
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

    inverseThresholdImpliesSmallCoupling : ∀ scale →
      inverseThreshold ≤ Flow.inverseCoupling trajectory scale →
      couplingAt scale ≤ gamma

open BetaSplitTerminalHistoryData public

asTerminalHistory :
  ∀ {trajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory} →
  BetaSplitTerminalHistoryData trajectory split →
  Terminal.TerminalInverseThresholdHistory trajectory
asTerminalHistory {split = split} dataSet = record
  { Terminal.TerminalInverseThresholdHistory.couplingAt = couplingAt dataSet
  ; Terminal.TerminalInverseThresholdHistory.gamma = gamma dataSet
  ; Terminal.TerminalInverseThresholdHistory.inverseThreshold =
      inverseThreshold dataSet
  ; Terminal.TerminalInverseThresholdHistory.terminalScale = terminalScale dataSet
  ; Terminal.TerminalInverseThresholdHistory.ActiveScale = ActiveScale dataSet
  ; Terminal.TerminalInverseThresholdHistory.terminalActive = terminalActive dataSet
  ; Terminal.TerminalInverseThresholdHistory.gapToTerminal = gapToTerminal dataSet
  ; Terminal.TerminalInverseThresholdHistory.scaleReachesTerminal =
      scaleReachesTerminal dataSet
  ; Terminal.TerminalInverseThresholdHistory.terminalInverseThreshold =
      terminalInverseThreshold dataSet
  ; Terminal.TerminalInverseThresholdHistory.betaNonnegative =
      Monotone.betaSplitAsNonnegativeTrajectory split
  ; Terminal.TerminalInverseThresholdHistory.inverseThresholdImpliesSmallCoupling =
      inverseThresholdImpliesSmallCoupling dataSet
  }

betaSplitTerminalThresholdAtActiveScale :
  ∀ {trajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (dataSet : BetaSplitTerminalHistoryData trajectory split)
    scale → ActiveScale dataSet scale →
  inverseThreshold dataSet ≤ Flow.inverseCoupling trajectory scale
betaSplitTerminalThresholdAtActiveScale dataSet =
  Terminal.inverseThresholdAtActiveScale (asTerminalHistory dataSet)

betaSplitSmallCouplingAtActiveScale :
  ∀ {trajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (dataSet : BetaSplitTerminalHistoryData trajectory split)
    scale → ActiveScale dataSet scale →
  couplingAt dataSet scale ≤ gamma dataSet
betaSplitSmallCouplingAtActiveScale dataSet =
  Terminal.smallCouplingAtActiveScale (asTerminalHistory dataSet)

balabanBetaSplitTerminalHistoryAssemblyLevel : ProofLevel
balabanBetaSplitTerminalHistoryAssemblyLevel = machineChecked

balabanBetaSplitTerminalSmallCouplingLevel : ProofLevel
balabanBetaSplitTerminalSmallCouplingLevel = machineChecked
