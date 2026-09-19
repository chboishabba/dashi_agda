module DASHI.Moonshine.JInvariantBishopPolynomialGeometricRatioValidation where

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopArchimedeanLinearAbsorptionExact as Absorb
import DASHI.Moonshine.JInvariantBishopPolynomialGeometricRatioExact as P

degreeFourAbsoluteConvergence :
  ∀ {ratio largerRatio : BishopReal.ℝ} →
  Absorb.BishopStrictRatioPair ratio largerRatio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.degreeFourTerm ratio)
degreeFourAbsoluteConvergence =
  P.degreeFourAbsoluteConvergence

degreeSixAbsoluteConvergence :
  ∀ {ratio largerRatio : BishopReal.ℝ} →
  Absorb.BishopStrictRatioPair ratio largerRatio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.degreeSixTerm ratio)
degreeSixAbsoluteConvergence =
  P.degreeSixAbsoluteConvergence
