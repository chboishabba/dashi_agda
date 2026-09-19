module DASHI.Moonshine.JInvariantBishopPolynomialGeometricRatioValidation where

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopArchimedeanLinearAbsorptionExact as Absorb
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
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


degreeFourUnitRatioAbsoluteConvergence :
  ∀ {ratio : BishopReal.ℝ} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.degreeFourTerm ratio)
degreeFourUnitRatioAbsoluteConvergence =
  P.degreeFourUnitRatioAbsoluteConvergence

degreeSixUnitRatioAbsoluteConvergence :
  ∀ {ratio : BishopReal.ℝ} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.degreeSixTerm ratio)
degreeSixUnitRatioAbsoluteConvergence =
  P.degreeSixUnitRatioAbsoluteConvergence
