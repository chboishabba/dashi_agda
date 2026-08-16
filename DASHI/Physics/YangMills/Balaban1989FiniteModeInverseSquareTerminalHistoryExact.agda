module DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact where

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
-- Direct L3/L4 -> CMP122 bridge.  Unlike the older beta-split history, this
-- module does not accept global fields betaZ>=b* or |betaInt|<=b*/2.  It starts
-- from the finite per-mode Gaussian/per-atom interaction producer and obtains
-- beta>=0 from those local estimates.  The already machine-checked rational
-- inverse-square order theorem then turns one terminal inverse threshold into
-- g_k<=gamma on every active scale.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; Positive; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.Balaban1989TerminalInverseThresholdHistoryExact as History

record FiniteModeInverseSquareTerminalHistoryData
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (Mode Atom : Set)
    (betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom) : Set₁ where
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

open FiniteModeInverseSquareTerminalHistoryData public

orderDataAtScale :
  ∀ {trajectory Mode Atom betaData} →
  FiniteModeInverseSquareTerminalHistoryData
    trajectory Mode Atom betaData →
  Nat → Order.RationalInverseSquareOrderData
orderDataAtScale {trajectory} dataSet scale = record
  { Order.RationalInverseSquareOrderData.coupling = couplingAt dataSet scale
  ; Order.RationalInverseSquareOrderData.thresholdCoupling = gamma dataSet
  ; Order.RationalInverseSquareOrderData.inverseCoupling =
      Flow.inverseCoupling trajectory scale
  ; Order.RationalInverseSquareOrderData.inverseThreshold =
      inverseThreshold dataSet
  ; Order.RationalInverseSquareOrderData.couplingPositive =
      couplingPositive dataSet scale
  ; Order.RationalInverseSquareOrderData.thresholdCouplingPositive =
      gammaPositive dataSet
  ; Order.RationalInverseSquareOrderData.inverseCouplingTimesSquare =
      inverseCouplingRepresentation dataSet scale
  ; Order.RationalInverseSquareOrderData.inverseThresholdTimesSquare =
      inverseThresholdRepresentation dataSet
  }

asTerminalHistory :
  ∀ {trajectory Mode Atom betaData} →
  FiniteModeInverseSquareTerminalHistoryData
    trajectory Mode Atom betaData →
  History.TerminalInverseThresholdHistory trajectory
asTerminalHistory {betaData = betaData} dataSet = record
  { History.TerminalInverseThresholdHistory.couplingAt = couplingAt dataSet
  ; History.TerminalInverseThresholdHistory.gamma = gamma dataSet
  ; History.TerminalInverseThresholdHistory.inverseThreshold =
      inverseThreshold dataSet
  ; History.TerminalInverseThresholdHistory.terminalScale = terminalScale dataSet
  ; History.TerminalInverseThresholdHistory.ActiveScale = ActiveScale dataSet
  ; History.TerminalInverseThresholdHistory.terminalActive = terminalActive dataSet
  ; History.TerminalInverseThresholdHistory.gapToTerminal = gapToTerminal dataSet
  ; History.TerminalInverseThresholdHistory.scaleReachesTerminal =
      scaleReachesTerminal dataSet
  ; History.TerminalInverseThresholdHistory.terminalInverseThreshold =
      terminalInverseThreshold dataSet
  ; History.TerminalInverseThresholdHistory.betaNonnegative =
      FiniteBeta.finiteModesAsNonnegativeBetaTrajectory betaData
  ; History.TerminalInverseThresholdHistory.inverseThresholdImpliesSmallCoupling =
      λ scale thresholdBelow →
        Order.inverseSquareThresholdImpliesSmallCoupling
          (orderDataAtScale dataSet scale) thresholdBelow
  }

finiteModeTerminalThresholdAtActiveScale :
  ∀ {trajectory Mode Atom betaData}
    (dataSet : FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData)
    scale → ActiveScale dataSet scale →
  inverseThreshold dataSet ≤ Flow.inverseCoupling trajectory scale
finiteModeTerminalThresholdAtActiveScale dataSet =
  History.inverseThresholdAtActiveScale (asTerminalHistory dataSet)

finiteModeSmallCouplingAtActiveScale :
  ∀ {trajectory Mode Atom betaData}
    (dataSet : FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData)
    scale → ActiveScale dataSet scale →
  couplingAt dataSet scale ≤ gamma dataSet
finiteModeSmallCouplingAtActiveScale dataSet =
  History.smallCouplingAtActiveScale (asTerminalHistory dataSet)

balabanFiniteModeTerminalHistoryAssemblyLevel : ProofLevel
balabanFiniteModeTerminalHistoryAssemblyLevel = machineChecked

balabanFiniteModeSmallCouplingHistoryLevel : ProofLevel
balabanFiniteModeSmallCouplingHistoryLevel = machineChecked
