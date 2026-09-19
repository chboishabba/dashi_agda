module DASHI.Moonshine.JInvariantBishopTrigUnitPhaseValidation where

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Moonshine.JInvariantBishopTrigUnitPhaseExact as P

unitPhaseRegression :
  (dataSet : Elementary.BishopElementaryPowerSeriesData) →
  (angle : BishopReal.ℝ) →
  P.BishopTrigPythagoreanAt dataSet angle →
  BishopReal._≃_
    (Norm.normSqC (P.bishopTrigPhase dataSet angle))
    BishopReal.1ℝ
unitPhaseRegression =
  P.bishopTrigPhaseUnit
