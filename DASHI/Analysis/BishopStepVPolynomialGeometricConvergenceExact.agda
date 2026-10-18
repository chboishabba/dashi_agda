module DASHI.Analysis.BishopStepVPolynomialGeometricConvergenceExact where

------------------------------------------------------------------------
-- STEP-V POLYNOMIAL/GEOMETRIC DOMINATION -> BISHOP CONVERGENCE
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The Yang--Mills Step-V lane already packages the exact pointwise theorem:
--
--   weightedTerm(n) <= M * rho^n
--
-- with rho<1 and all weighted terms nonnegative.  The Analysis-level
-- BishopGeometricMajorantSeriesConvergenceExact module already proves that any
-- series absolutely dominated by M*rho^n converges once 0<rho<1.
--
-- This owner welds those two existing interfaces.  It adds no analytic axiom.
-- Positivity of the chosen larger ratio is explicit because the Step-V record
-- only stores nonnegativity through its finite-geometric bound.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopGeometricMajorantSeriesConvergenceExact as Majorant
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVPolynomialWeightedDominationExact as Weighted
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopStepV
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The generic Step-V power multiplies on the left, while vendor/bishop's pow
-- recurses on the right.  Commutativity identifies them extensionally.
------------------------------------------------------------------------

stepVPowerIsBishopPower :
  ∀ ratio index →
  BishopReal._≃_
    (StepV.power
      BishopStepV.bishopOrderedSemiringKernel
      ratio index)
    (BishopReal.pow ratio index)
stepVPowerIsBishopPower ratio zero =
  BishopP.≃-refl
stepVPowerIsBishopPower ratio (suc index) =
  BishopP.≃-trans
    (BishopP.*-congˡ
      (stepVPowerIsBishopPower ratio index))
    (BishopP.*-comm
      ratio
      (BishopReal.pow ratio index))

weightedTermAbsIsSelf :
  ∀ {ratio degree}
    (inputs : Weighted.PolynomialGeometricDomination
      BishopStepV.bishopOrderedSemiringKernel
      BishopStepV.bishopGeometricSemiringLaws
      ratio degree) →
  ∀ index →
  BishopReal._≃_
    (BishopReal.∣_∣ (Weighted.weightedTerm inputs index))
    (Weighted.weightedTerm inputs index)
weightedTermAbsIsSelf inputs index =
  BishopP.nonNegx⇒∣x∣≃x
    (BishopP.0≤x⇒nonNegx
      (Weighted.weightedTermNonnegative inputs index))

stepVMajorantIsBishopMajorant :
  ∀ {ratio degree}
    (inputs : Weighted.PolynomialGeometricDomination
      BishopStepV.bishopOrderedSemiringKernel
      BishopStepV.bishopGeometricSemiringLaws
      ratio degree) →
  ∀ index →
  BishopReal._≃_
    (BishopReal._*_
      (Weighted.dominationConstant inputs)
      (StepV.power
        BishopStepV.bishopOrderedSemiringKernel
        (Weighted.chosenLargerRatio inputs)
        index))
    (Majorant.scaledGeometricTerm
      (Weighted.dominationConstant inputs)
      (Weighted.chosenLargerRatio inputs)
      index)
stepVMajorantIsBishopMajorant inputs index =
  BishopP.*-congˡ
    (stepVPowerIsBishopPower
      (Weighted.chosenLargerRatio inputs)
      index)

weightedTermBelowBishopGeometricMajorant :
  ∀ {ratio degree}
    (inputs : Weighted.PolynomialGeometricDomination
      BishopStepV.bishopOrderedSemiringKernel
      BishopStepV.bishopGeometricSemiringLaws
      ratio degree) →
  ∀ index →
  BishopReal._≤_
    (BishopReal.∣_∣ (Weighted.weightedTerm inputs index))
    (Majorant.scaledGeometricTerm
      (Weighted.dominationConstant inputs)
      (Weighted.chosenLargerRatio inputs)
      index)
weightedTermBelowBishopGeometricMajorant inputs index =
  BishopP.≤-respʳ-≃
    (stepVMajorantIsBishopMajorant inputs index)
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm (weightedTermAbsIsSelf inputs index))
      (Weighted.pointwisePolynomialGeometricDomination
        inputs index))

dominationConstantNonnegativeBishop :
  ∀ {ratio degree}
    (inputs : Weighted.PolynomialGeometricDomination
      BishopStepV.bishopOrderedSemiringKernel
      BishopStepV.bishopGeometricSemiringLaws
      ratio degree) →
  BishopReal.NonNegative (Weighted.dominationConstant inputs)
dominationConstantNonnegativeBishop inputs =
  BishopP.0≤x⇒nonNegx
    (Weighted.dominationConstantNonnegative inputs)

chosenLargerRatioBelowOne :
  ∀ {ratio degree}
    (inputs : Weighted.PolynomialGeometricDomination
      BishopStepV.bishopOrderedSemiringKernel
      BishopStepV.bishopGeometricSemiringLaws
      ratio degree) →
  BishopReal._<_
    (Weighted.chosenLargerRatio inputs)
    BishopReal.1ℝ
chosenLargerRatioBelowOne inputs =
  StepV.ratioBelowOne (Weighted.largerRatioBound inputs)

stepVPolynomialGeometricSeriesConvergent :
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
stepVPolynomialGeometricSeriesConvergent inputs largerRatioPositive =
  Majorant.seriesConvergentFromScaledGeometricMajorant
    (Weighted.weightedTerm inputs)
    (Weighted.chosenLargerRatio inputs)
    (Weighted.dominationConstant inputs)
    largerRatioPositive
    (chosenLargerRatioBelowOne inputs)
    (dominationConstantNonnegativeBishop inputs)
    (weightedTermBelowBishopGeometricMajorant inputs)

stepVToBishopConvergenceCompilerLevel : ProofLevel
stepVToBishopConvergenceCompilerLevel = conditional
