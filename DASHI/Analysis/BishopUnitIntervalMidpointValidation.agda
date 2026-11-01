module DASHI.Analysis.BishopUnitIntervalMidpointValidation where

import Real as BishopReal

import DASHI.Analysis.BishopArchimedeanLinearAbsorptionExact as Absorb
import DASHI.Analysis.BishopUnitIntervalMidpointExact as M
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit

midpointPair :
  ∀ {ratio : BishopReal.ℝ} →
  Unit.BishopUnitIntervalRatio ratio →
  Absorb.BishopStrictRatioPair ratio (M.midpointToOne ratio)
midpointPair = M.canonicalMidpointRatioPair
