module DASHI.Analysis.BishopRound11TrigModulusFromPythagoreanExact where

------------------------------------------------------------------------
-- K05 -> K04d SAME-OBJECT TRIG MODULUS COMPILER.
--
-- The original Bishop sine/cosine at each point give an actual
-- Cartesian complex phase. Existing Moonshine and norm-square proof
-- owners prove c² <= c²+s² and s² <= c²+s².
--
-- From the REAL Round11 Pythagorean equation c²+s² ≃ 1,
-- the pinned native constructive NONNEGATIVE-SQUARE-REFLECTION
-- theorem establishes |cos|<=1 and |sin|<=1. No classical sqrt,
-- arbitrary complex absolute value, or new trig realization.
--
-- This discharges K04d's phase-modulus gate *conditional only* on
-- the original Round11 Pythagorean theorem, not the logarithm
-- inverse or any zeta-continuity oracle.
--
-- Original authors/owners: Bishop/Bridges, Murray, Viktor Csimma;
-- DASHI/Analysis/BishopComplexNormSquarePowerEnvelopeExact;
-- DASHI/Foundations/BishopNonnegativeSquareReflectionExact;
-- DASHI/Moonshine/JInvariantBishopTrigUnitPhaseExact.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflection
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as NegativeExp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Moonshine.JInvariantBishopTrigUnitPhaseExact as Phase
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

oneNonnegative : R.NonNegative R.1ℝ
oneNonnegative =
  RP.0≤x⇒nonNegx (RP.<⇒≤ NegativeExp.onePositive)

bishopTrigCosAbsoluteBelowOne :
  (dataSet : E.BishopElementaryPowerSeriesData) →
  (angle : R.ℝ) →
  Phase.BishopTrigPythagoreanAt dataSet angle →
  R._≤_
    (R.∣ E.bishopCos dataSet angle ∣)
    R.1ℝ
bishopTrigCosAbsoluteBelowOne dataSet angle certificate =
  let
    c = E.bishopCos dataSet angle
    p = Phase.bishopTrigPhase dataSet angle
    squared :
      R._≤_
        (Norm.square (R.∣ c ∣))
        (Norm.square R.1ℝ)
    squared =
      RP.≤-respˡ-≃
        (RP.≃-symm (Norm.absoluteSquare c))
        (RP.≤-respʳ-≃
          (RP.≃-symm (RP.*-identityʳ R.1ℝ))
          (RP.≤-respʳ-≃
            (Phase.bishopTrigPhaseUnit dataSet angle certificate)
            (Norm.componentSquareBelowNormSqReal p)))
  in
  Reflection.squareReflectsOnNonnegative
    (RP.nonNeg∣x∣ c)
    oneNonnegative
    squared

bishopTrigSinAbsoluteBelowOne :
  (dataSet : E.BishopElementaryPowerSeriesData) →
  (angle : R.ℝ) →
  Phase.BishopTrigPythagoreanAt dataSet angle →
  R._≤_
    (R.∣ E.bishopSin dataSet angle ∣)
    R.1ℝ
bishopTrigSinAbsoluteBelowOne dataSet angle certificate =
  let
    s = E.bishopSin dataSet angle
    p = Phase.bishopTrigPhase dataSet angle
    squared :
      R._≤_
        (Norm.square (R.∣ s ∣))
        (Norm.square R.1ℝ)
    squared =
      RP.≤-respˡ-≃
        (RP.≃-symm (Norm.absoluteSquare s))
        (RP.≤-respʳ-≃
          (RP.≃-symm (RP.*-identityʳ R.1ℝ))
          (RP.≤-respʳ-≃
            (Phase.bishopTrigPhaseUnit dataSet angle certificate)
            (Norm.componentSquareBelowNormSqImag p)))
  in
  Reflection.squareReflectsOnNonnegative
    (RP.nonNeg∣x∣ s)
    oneNonnegative
    squared

-- The exact selected Round11 signed-factorial functions. The input
-- Pythagorean is a REAL equation on that same Round11 carrier.
round11ModulusFromPythagorean :
  (inputs : Round11.Round11BishopCutset) →
  (angle : R.ℝ) →
  let
    dataSet = Round11.elementarySeries inputs
    c = E.bishopCos dataSet angle
    s = E.bishopSin dataSet angle
  in
  R._≃_
    (R._+_ (R._*_ c c) (R._*_ s s))
    R.1ℝ →
  (R._≤_ (R.∣ c ∣) R.1ℝ)
  ×
  (R._≤_ (R.∣ s ∣) R.1ℝ)
round11ModulusFromPythagorean inputs angle pythagorean =
  let
    dataSet = Round11.elementarySeries inputs
    certificate : Phase.BishopTrigPythagoreanAt dataSet angle
    certificate = record { Phase.pythagorean = pythagorean }
  in
  bishopTrigCosAbsoluteBelowOne dataSet angle certificate
  ,
  bishopTrigSinAbsoluteBelowOne dataSet angle certificate
