{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityS4TwoSeamNoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact as UnitCap
import DASHI.Physics.Foundations.CMP119AntigravityUnitThresholdClosesSU2NoGoExact as SU2Threshold
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta

------------------------------------------------------------------------
-- AG-S4 FINAL ARITHMETIC CUT
--
-- All inequality analysis is compiler-owned after TWO semantic seams:
--
--   S4a  the selected finite-history gamma is identified with a cap <= 1;
--   S4b  the physical SU(2) anomaly threshold is in the SAME inverse-coupling
--        normalization as the history threshold and is bounded by the normalized
--        rational 11/24 coefficient.
--
-- Then
--
--   gamma <= 1
--     -> 1 <= u_*
--     -> 11/24 <= u_*
--
-- and the active-scale history propagation gives the weak-coupling no-go.
------------------------------------------------------------------------

historyUnitCapPaysNormalizedSU2Threshold :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    (history :
      History.FiniteModeInverseSquareTerminalHistoryData
        trajectory Mode Atom betaData) →
  History.gamma history ≤ 1ℚ →
  SU2Threshold.Coeff.selectedWeakCouplingNoGoThresholdRational
    ≤ History.inverseThreshold history
historyUnitCapPaysNormalizedSU2Threshold history gammaBelowOne =
  SU2Threshold.unitInverseThresholdPaysNormalizedSU2Threshold
    (UnitCap.historyInverseThresholdAtLeastOneFromUnitGamma
      history gammaBelowOne)

newS4InequalityAnalysisRequired : Bool
newS4InequalityAnalysisRequired = false

historyGammaSameObjectUnitCapStillRequired : Bool
historyGammaSameObjectUnitCapStillRequired = true

physicalAnomalyToHistoryNormalizationStillRequired : Bool
physicalAnomalyToHistoryNormalizationStillRequired = true

newS4InequalityAnalysisRequiredIsFalse :
  newS4InequalityAnalysisRequired ≡ false
newS4InequalityAnalysisRequiredIsFalse = refl

historyGammaSameObjectUnitCapStillRequiredIsTrue :
  historyGammaSameObjectUnitCapStillRequired ≡ true
historyGammaSameObjectUnitCapStillRequiredIsTrue = refl

physicalAnomalyToHistoryNormalizationStillRequiredIsTrue :
  physicalAnomalyToHistoryNormalizationStillRequired ≡ true
physicalAnomalyToHistoryNormalizationStillRequiredIsTrue = refl
