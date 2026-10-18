module DASHI.Analysis.BishopPolynomialGeometricComparisonValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopPolynomialGeometricComparisonExact as P
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopStepV
import DASHI.Physics.YangMills.BalabanStepVPolynomialDirectRatioExact as Direct

directRatioToAbsoluteConvergence :
  ∀ {ratio : BishopReal.ℝ} {degree : Nat} →
  (inputs :
    Direct.PolynomialDirectRatioInputs
      BishopStepV.bishopOrderedSemiringKernel
      BishopStepV.bishopGeometricSemiringLaws
      ratio degree) →
  BishopReal._<_ BishopReal.0ℝ
    (Direct.chosenLargerRatio inputs) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Direct.weightedTerm inputs)
directRatioToAbsoluteConvergence =
  P.bishopAbsoluteConvergenceFromDirectRatio
