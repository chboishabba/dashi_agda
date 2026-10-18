module DASHI.Moonshine.JInvariantBishopTrigUnitPhaseExact where

------------------------------------------------------------------------
-- BISHOP TRIGONOMETRIC UNIT PHASE
--
-- DASHI CONTRIBUTION
--
-- Given one Bishop elementary power-series dataset and one Pythagorean
-- certificate at an angle theta, the canonical complex phase
--
--   cos(theta) + i sin(theta)
--
-- has norm-square one on the concrete Bishop complex carrier.
--
-- This isolates phase semantics from the Eisenstein convergence proof:
-- the latter consumes only a unit phase and does not depend on how the
-- Pythagorean theorem is obtained.
------------------------------------------------------------------------

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary

bishopTrigPhase :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ →
  Complex.BishopComplex
bishopTrigPhase dataSet angle =
  Complex.complex
    (Elementary.bishopCos dataSet angle)
    (Elementary.bishopSin dataSet angle)

record BishopTrigPythagoreanAt
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (angle : BishopReal.ℝ) : Set where
  field
    pythagorean :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_
            (Elementary.bishopCos dataSet angle)
            (Elementary.bishopCos dataSet angle))
          (BishopReal._*_
            (Elementary.bishopSin dataSet angle)
            (Elementary.bishopSin dataSet angle)))
        BishopReal.1ℝ

open BishopTrigPythagoreanAt public

bishopTrigPhaseUnit :
  (dataSet : Elementary.BishopElementaryPowerSeriesData) →
  (angle : BishopReal.ℝ) →
  BishopTrigPythagoreanAt dataSet angle →
  BishopReal._≃_
    (Norm.normSqC (bishopTrigPhase dataSet angle))
    BishopReal.1ℝ
bishopTrigPhaseUnit dataSet angle certificate =
  pythagorean certificate
