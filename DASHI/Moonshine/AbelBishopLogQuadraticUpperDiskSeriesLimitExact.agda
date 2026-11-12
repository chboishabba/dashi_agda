module DASHI.Moonshine.AbelBishopLogQuadraticUpperDiskSeriesLimitExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP LOG(1+w): QUADRATIC TAIL CONVERGENCE ON CLOSED DISKS.
--
-- The original source log series already converges absolutely at EVERY
-- original upper-disk point: normSq(w) <= ratio², 0 <= ratio < 1.
-- The old quadratic-tail limit owner demanded normSq(w) ~= ratio²,
-- an exact-radius input unavailable at the selected local log chart.
--
-- This module discharges THAT genuine analytic mismatch: the original
-- shifted degree >= 2 source stream converges to the actual upper-disk
-- log series limit minus w, with no equality radius and no new log.
--
-- This DOES NOT prove the quantitative |R₂| <= (8/27)|w|²,
-- principal log inverse, fixed point, global Abel/Kneser, or RH.
-- Source-written; original Agda 2.9 kernel receipt still required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact as Continuity
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopInverseKoenigsShiftConvergenceExact as Shift
import DASHI.Moonshine.AbelBishopInverseKoenigsRemainderFactorExact as Ring
import DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact as Finite
import DASHI.Moonshine.AbelBishopLogQuadraticSeriesLimitExact as Tail
import DASHI.Moonshine.AbelBishopLogOnePlusUpperDiskConvergenceExact as UpperLog

originalBishopUpperDiskQuadraticRemainder :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  Upper.BishopComplexNormSquareUpperRadius w ratio →
  Complex.BishopComplex
originalBishopUpperDiskQuadraticRemainder {w} interval disk =
  Algebra._-C_
    (UpperLog.originalBishopLogUpperDiskCanonicalValue interval disk)
    w

originalBishopUpperDiskFullPrefixConverges :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Completion.OriginalBishopPointwiseComplexConverges
    (Finite.originalBishopLogFinitePrefix w)
    (UpperLog.originalBishopLogUpperDiskCanonicalValue interval disk)
originalBishopUpperDiskFullPrefixConverges interval disk =
  let source = UpperLog.originalBishopLogUpperDiskCanonicalConverges interval disk
  in Completion.original-bishop-pointwise-complex-converges
    (Complex.realConverges source)
    (Complex.imagConverges source)

originalBishopUpperDiskQuadraticTailConverges :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  Completion.OriginalBishopPointwiseComplexConverges
    (Finite.originalBishopLogQuadraticTailPrefix w)
    (originalBishopUpperDiskQuadraticRemainder interval disk)
originalBishopUpperDiskQuadraticTailConverges {w} interval disk =
  let
    full = Finite.originalBishopLogFinitePrefix w
    value = UpperLog.originalBishopLogUpperDiskCanonicalValue interval disk

    shifted =
      Shift.originalBishopComplexSuccessorConvergesToSame
        full value
        (originalBishopUpperDiskFullPrefixConverges interval disk)

    realMinus =
      Continuity.originalBishopSubtractConverges
        (λ n → Complex.re (full (suc n)))
        (λ n → Complex.re w)
        (Complex.re value) (Complex.re w)
        (Completion.realConverges shifted)
        (Continuity.originalBishopConstantSequenceConverges
          (Complex.re w))

    imagMinus =
      Continuity.originalBishopSubtractConverges
        (λ n → Complex.im (full (suc n)))
        (λ n → Complex.im w)
        (Complex.im value) (Complex.im w)
        (Completion.imaginaryConverges shifted)
        (Continuity.originalBishopConstantSequenceConverges
          (Complex.im w))
  in
  Completion.original-bishop-pointwise-complex-converges
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n → proj₁ (Tail.originalBishopLogPrefixMinusFirstIsQuadraticTail w n))
      (Complex.re (originalBishopUpperDiskQuadraticRemainder interval disk) ,
        realMinus))
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n → proj₂ (Tail.originalBishopLogPrefixMinusFirstIsQuadraticTail w n))
      (Complex.im (originalBishopUpperDiskQuadraticRemainder interval disk) ,
        imagMinus))
