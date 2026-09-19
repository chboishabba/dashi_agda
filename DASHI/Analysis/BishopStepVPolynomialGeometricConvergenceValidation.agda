module DASHI.Analysis.BishopStepVPolynomialGeometricConvergenceValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Physics.YangMills.BalabanStepVPolynomialWeightedDominationExact as Weighted
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopStepV
import DASHI.Analysis.BishopStepVPolynomialGeometricConvergenceExact as P

stepVConvergenceRegression :
  ∀ {ratio : BishopReal.ℝ} {degree : Nat} →
  (inputs : Weighted.PolynomialGeometricDomination
    BishopStepV.bishopOrderedSemiringKernel
    BishopStepV.bishopGeometricSemiringLaws
    ratio degree) →
  BishopReal._<_
    BishopReal.0ℝ
    (Weighted.chosenLargerRatio inputs) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (Weighted.weightedTerm inputs))
stepVConvergenceRegression =
  P.stepVPolynomialGeometricSeriesConvergent
