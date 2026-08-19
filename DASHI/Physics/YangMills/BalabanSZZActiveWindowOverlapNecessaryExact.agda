module DASHI.Physics.YangMills.BalabanSZZActiveWindowOverlapNecessaryExact where

------------------------------------------------------------------------
-- ROUND68: NECESSARY ACTIVE-WINDOW OVERLAP FOR THE BALABAN -> SZZ HANDOFF
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- DASHI CONTRIBUTION
--
-- The proposed UV->IR handoff is possible only if the rigorous source windows
-- overlap.  On every active Bałaban scale the terminal-history theorem gives
--
--      u_B <= u_k,
--
-- where u_B is the inverse-coupling small-g threshold.  A pure-Wilson SZZ
-- crossover asks for
--
--      u_k <= u_* < N^2/48.
--
-- Hence necessarily
--
--      u_B < N^2/48.
--
-- This theorem prevents a formal crossover target from being placed beyond the
-- proven CMP119/CMP122 validity window.  The repository currently keeps u_B
-- abstract, so numerical overlap is NOT claimed here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.Balaban1989TerminalInverseThresholdHistoryExact as History
import DASHI.Physics.YangMills.BalabanSZZWilsonCrossoverTerminalGapExact as Cross

record ActiveWindowCrossover
    (rank : Cross.RationalRankNormalization)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (history : History.TerminalInverseThresholdHistory trajectory) : Set where
  field
    scale : Nat
    active : History.ActiveScale history scale
    targetInverseCoupling : ℚ

    actualBelowTarget :
      Flow.inverseCoupling trajectory scale ≤ targetInverseCoupling

    targetInsidePureWilsonSZZWindow :
      targetInverseCoupling < Cross.szzInverseCouplingThreshold rank
open ActiveWindowCrossover public

balabanThresholdBelowCrossoverTarget :
  ∀ {rank trajectory history}
    (dataSet : ActiveWindowCrossover rank trajectory history) →
  History.inverseThreshold history ≤ targetInverseCoupling dataSet
balabanThresholdBelowCrossoverTarget {history = history} dataSet =
  ℚP.≤-trans
    (History.inverseThresholdAtActiveScale history
      (scale dataSet) (active dataSet))
    (actualBelowTarget dataSet)

balabanThresholdMustOverlapPureWilsonSZZWindow :
  ∀ {rank trajectory history}
    (dataSet : ActiveWindowCrossover rank trajectory history) →
  History.inverseThreshold history
  < Cross.szzInverseCouplingThreshold rank
balabanThresholdMustOverlapPureWilsonSZZWindow dataSet =
  ℚP.≤-<-trans
    (balabanThresholdBelowCrossoverTarget dataSet)
    (targetInsidePureWilsonSZZWindow dataSet)

balabanSZZWindowOverlapNecessityLevel : ProofLevel
balabanSZZWindowOverlapNecessityLevel = machineChecked

-- Source-native numerical overlap (or an extension of the RG theorem through
-- the intermediate-coupling region) remains a real analytic obligation.
physicalBalabanSZZWindowOverlapLevel : ProofLevel
physicalBalabanSZZWindowOverlapLevel = conditional
