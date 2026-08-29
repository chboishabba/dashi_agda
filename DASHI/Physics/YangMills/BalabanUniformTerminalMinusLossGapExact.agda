module DASHI.Physics.YangMills.BalabanUniformTerminalMinusLossGapExact where

------------------------------------------------------------------------
-- ROUND66: ONE TERMINAL FLOOR - ONE LOSS CEILING = ONE COMMON MASS FLOOR
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Martin Luscher,
-- "Construction of a Selfadjoint, Strictly Positive Transfer Matrix for
-- Euclidean Lattice Gauge Theories", Communications in Mathematical Physics
-- 54 (1977), 283--292. DOI: 10.1007/BF01614090.
--
-- Volker Bach, Thomas Chen, Juerg Froehlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group Methods",
-- Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Tosio Kato, "Perturbation Theory for Linear Operators".
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Sharpen leaves L5--L6 to the exact numerical theorem the physical analysis
-- must deliver.  It is sufficient to prove, uniformly in cutoff,
--
--   m0 <= terminalGap_n,
--   totalLoss_n <= ell,
--   ell < m0,
--   terminalGap_n - totalLoss_n <= physicalGap_n.
--
-- Then mStar = m0-ell is strictly positive and lies below EVERY physical gap.
-- No separate common-floor witness is needed after those inequalities.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCutoffUniformPhysicalTransferGapMasterExact as Master

record UniformTerminalMinusLossBudget : Set₁ where
  field
    terminalGapAt totalLossAt physicalGapAt : Nat → ℚ
    terminalFloor lossCeiling : ℚ

    lossCeilingStrictlyBelowTerminalFloor : lossCeiling < terminalFloor

    terminalFloorUniform : ∀ cutoff →
      terminalFloor ≤ terminalGapAt cutoff

    lossCeilingUniform : ∀ cutoff →
      totalLossAt cutoff ≤ lossCeiling

    pulledBackGapBelowPhysical : ∀ cutoff →
      terminalGapAt cutoff - totalLossAt cutoff ≤ physicalGapAt cutoff

open UniformTerminalMinusLossBudget public

commonMassFloor : UniformTerminalMinusLossBudget → ℚ
commonMassFloor dataSet = terminalFloor dataSet - lossCeiling dataSet

commonMassFloorPositive :
  (dataSet : UniformTerminalMinusLossBudget) →
  0ℚ < commonMassFloor dataSet
commonMassFloorPositive dataSet =
  subst
    (λ right → 0ℚ < right)
    (ℚRing.solve-∀ (terminalFloor dataSet) (lossCeiling dataSet))
    (subst
      (λ left → left < terminalFloor dataSet + (- lossCeiling dataSet))
      (ℚRing.solve-∀ (lossCeiling dataSet))
      (ℚP.+-monoʳ-<
        (- lossCeiling dataSet)
        (lossCeilingStrictlyBelowTerminalFloor dataSet)))

commonFloorBelowPulledBack :
  (dataSet : UniformTerminalMinusLossBudget) →
  ∀ cutoff →
  commonMassFloor dataSet
  ≤ terminalGapAt dataSet cutoff - totalLossAt dataSet cutoff
commonFloorBelowPulledBack dataSet cutoff =
  let
    terminalBound = terminalFloorUniform dataSet cutoff
    lossBound = lossCeilingUniform dataSet cutoff
    signed = ℚP.+-mono-≤ terminalBound (ℚP.neg-mono-≤ lossBound)
  in
  subst
    (λ left → left
      ≤ terminalGapAt dataSet cutoff - totalLossAt dataSet cutoff)
    (ℚRing.solve-∀ (terminalFloor dataSet) (lossCeiling dataSet))
    (subst
      (λ right →
        terminalFloor dataSet + (- lossCeiling dataSet) ≤ right)
      (ℚRing.solve-∀
        (terminalGapAt dataSet cutoff) (totalLossAt dataSet cutoff))
      signed)

uniformPhysicalGapFromTerminalMinusLoss :
  UniformTerminalMinusLossBudget → Master.CutoffUniformPhysicalTransferGap
uniformPhysicalGapFromTerminalMinusLoss dataSet = record
  { Master.CutoffUniformPhysicalTransferGap.physicalGapAt =
      physicalGapAt dataSet
  ; Master.CutoffUniformPhysicalTransferGap.massFloor =
      commonMassFloor dataSet
  ; Master.CutoffUniformPhysicalTransferGap.massFloorPositive =
      commonMassFloorPositive dataSet
  ; Master.CutoffUniformPhysicalTransferGap.massFloorBelowEveryCutoff =
      λ cutoff → ℚP.≤-trans
        (commonFloorBelowPulledBack dataSet cutoff)
        (pulledBackGapBelowPhysical dataSet cutoff)
  }

terminalMinusLossGapCompilerLevel : ProofLevel
terminalMinusLossGapCompilerLevel = machineChecked

-- Physical spectral theorem is now exactly a terminal floor and total-loss
-- ceiling on the literal transfer/Feshbach carrier.
physicalUniformTerminalFloorLevel : ProofLevel
physicalUniformTerminalFloorLevel = conditional

physicalUniformTotalLossCeilingLevel : ProofLevel
physicalUniformTotalLossCeilingLevel = conditional
