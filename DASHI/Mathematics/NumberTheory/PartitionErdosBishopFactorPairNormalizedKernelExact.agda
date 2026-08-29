module DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairNormalizedKernelExact where

------------------------------------------------------------------------
-- BASEL-FACING FACTOR-PAIR CUBIC KERNEL
--
-- Compose the local cubic degree-one kernel with reciprocal-square product
-- normalization.  The resulting right-hand side is already split into the
-- factor-index reciprocal square and the common x_n reciprocal square.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationFiniteDegreeOneKernelExact as Kernel
import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact as FactorResidual
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairInverseSquareNormalizationExact as Normalize
open import DASHI.Physics.YangMills.CompactLieProofLevel

factorPairNormalizedFiniteDegreeOneKernel :
  ∀ {n r : Nat} {nPositive : suc 0 ≤ n} →
  (rate : Rate.ErdosStepRate n nPositive) →
  (pair : Factor.PositiveFactorPair r) →
  ∀ count →
  let
    step = FactorResidual.factorStep rate pair
    stepPositive = FactorResidual.factorStepPositive rate pair
    copies = FactorResidual.factorCopies pair
  in
  BishopReal._<_
    (Identity.weightedPartial (Ratio.q step stepPositive) count)
    (BishopReal._*_
      (Reciprocal.inverseSquare
        (Iterated.natReal copies)
        (Reciprocal.xNonzero
          (Normalize.factorCopiesNatRealPositive pair)))
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
factorPairNormalizedFiniteDegreeOneKernel rate pair count =
  BishopP.<-respʳ-≃
    (Normalize.factorStepInverseSquareNormalization rate pair)
    (Kernel.cubicFiniteDegreeOneKernel
      (FactorResidual.factorStepPositive rate pair)
      count)

canonicalFactorPairNormalizedFiniteDegreeOneKernel :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  (pair : Factor.PositiveFactorPair r) →
  ∀ count →
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    step = FactorResidual.factorStep rate pair
    stepPositive = FactorResidual.factorStepPositive rate pair
    copies = FactorResidual.factorCopies pair
  in
  BishopReal._<_
    (Identity.weightedPartial (Ratio.q step stepPositive) count)
    (BishopReal._*_
      (Reciprocal.inverseSquare
        (Iterated.natReal copies)
        (Reciprocal.xNonzero
          (Normalize.factorCopiesNatRealPositive pair)))
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
canonicalFactorPairNormalizedFiniteDegreeOneKernel {n} nPositive pair count =
  factorPairNormalizedFiniteDegreeOneKernel
    (Rate.canonicalErdosStepRate n nPositive)
    pair count

partitionErdosBishopFactorPairNormalizedKernelLevel : ProofLevel
partitionErdosBishopFactorPairNormalizedKernelLevel = machineChecked
