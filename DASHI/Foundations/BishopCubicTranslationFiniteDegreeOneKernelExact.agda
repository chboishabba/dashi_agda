module DASHI.Foundations.BishopCubicTranslationFiniteDegreeOneKernelExact where

------------------------------------------------------------------------
-- CUBIC-TRANSLATION FINITE DEGREE-ONE KERNEL
--
-- For x>0 and q=D3(x)^(-1), every finite weighted geometric partial sum obeys
--
--   W_N(q) < x^(-2).
--
-- This composes the generic finite geometric bound with the cubic ratio cross
-- inequality; no exponential addition law and no infinite weighted-series
-- evaluation is used.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Cross
open import DASHI.Physics.YangMills.CompactLieProofLevel

cubicReciprocalSquareBound :
  ∀ {x} (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._<_
    (BishopReal._*_
      (Ratio.q x xPositive)
      (Cross.inverseSquare
        (Identity.oneMinus (Ratio.q x xPositive))
        (Cross.gapNonzero (Ratio.cubicRatioInputs xPositive))))
    (Cross.inverseSquare x (Cross.xNonzero xPositive))
cubicReciprocalSquareBound xPositive =
  Cross.reciprocalSquareFromCross
    xPositive
    (Ratio.cubicRatioInputs xPositive)
    (Ratio.qCrossInequality xPositive)

cubicFiniteDegreeOneKernel :
  ∀ {x} (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  ∀ count →
  BishopReal._<_
    (Identity.weightedPartial (Ratio.q x xPositive) count)
    (Cross.inverseSquare x (Cross.xNonzero xPositive))
cubicFiniteDegreeOneKernel xPositive count =
  BishopP.≤-<-trans
    (Geometric.finiteDegreeOneGeometricBound
      (Ratio.cubicRatioInputs xPositive) count)
    (cubicReciprocalSquareBound xPositive)

bishopCubicTranslationFiniteDegreeOneKernelLevel : ProofLevel
bishopCubicTranslationFiniteDegreeOneKernelLevel = machineChecked
