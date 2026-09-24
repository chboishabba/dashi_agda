module DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesValidation where

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as P

e4SetoidSeriesRegression :
  ∀ (q : Complex.BishopComplex) {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  P.BishopQPowerComponentEnvelope q ratio →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (P.e4BishopTerm q)
e4SetoidSeriesRegression =
  P.e4BishopComponentwiseAbsoluteConvergence

e6SetoidSeriesRegression :
  ∀ (q : Complex.BishopComplex) {ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  P.BishopQPowerComponentEnvelope q ratio →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (P.e6BishopUnsignedTerm q)
e6SetoidSeriesRegression =
  P.e6BishopComponentwiseAbsoluteConvergence

e4LimitRegression :
  ∀ (q : Complex.BishopComplex) {ratio}
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (envelope : P.BishopQPowerComponentEnvelope q ratio) →
  Complex.BishopComplex
e4LimitRegression q unit envelope =
  P.e4BishopLimit q unit envelope

e6LimitRegression :
  ∀ (q : Complex.BishopComplex) {ratio}
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (envelope : P.BishopQPowerComponentEnvelope q ratio) →
  Complex.BishopComplex
e6LimitRegression q unit envelope =
  P.e6BishopLimit q unit envelope

e4TailConvergenceRegression :
  ∀ (q : Complex.BishopComplex) {ratio}
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (envelope : P.BishopQPowerComponentEnvelope q ratio) →
  Complex.ComplexSeriesConvergesTo
    (P.e4BishopTerm q)
    (P.e4BishopTailLimit q unit envelope)
e4TailConvergenceRegression =
  P.e4BishopTailConvergence

e6TailConvergenceRegression :
  ∀ (q : Complex.BishopComplex) {ratio}
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (envelope : P.BishopQPowerComponentEnvelope q ratio) →
  Complex.ComplexSeriesConvergesTo
    (P.e6BishopUnsignedTerm q)
    (P.e6BishopUnsignedTailLimit q unit envelope)
e6TailConvergenceRegression =
  P.e6BishopUnsignedTailConvergence
