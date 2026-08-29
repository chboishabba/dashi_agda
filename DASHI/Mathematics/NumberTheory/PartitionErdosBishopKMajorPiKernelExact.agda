module DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorPiKernelExact where

------------------------------------------------------------------------
-- CONDITIONAL PI-NORMALIZED K-MAJOR ERDOS KERNEL
--
-- The finite k-major cubic kernel is already bounded by
--
--   BaselLimit * x_n^(-2).
--
-- The isolated sine-product coefficient boundary identifies BaselLimit with
-- pi_M^2/6.  The exact canonical-step cancellation then turns the right side
-- into the embedded Nat n.
--
-- Thus the ONLY analytic condition in this owner is the existing
-- `SineProductCoefficientLimit` certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopBaselSineProductCoefficientBoundaryExact as BaselBoundary
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorBaselLimitKernelExact as BaselKernel
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorMaskedKernelExact as KMajor
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopStepConstantCancellationExact as ConstantCancel
open import DASHI.Physics.YangMills.CompactLieProofLevel

kMajorMaskedKernelPiSquareBound :
  ∀ {n : Nat} →
  (nPositive : suc 0 ≤ n) →
  BaselBoundary.SineProductCoefficientLimit →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (KMajor.kMajorMaskedKernel rate)
    (BishopReal._*_
      BaselBoundary.piSquareOverSix
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
kMajorMaskedKernelPiSquareBound {n} nPositive certificate =
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    inv2 =
      Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))
    inv2NN =
      BishopP.pos⇒nonNeg
        (Reciprocal.inverseSquarePositive
          (Reciprocal.xNonzero (Rate.stepPositive rate))
          (Rate.stepPositive rate))
    baselEquality =
      BaselBoundary.baselFromSineProductCoefficientLimit certificate
    scaledEquality = BishopP.*-congʳ baselEquality
  in
  BishopP.≤-respʳ-≃
    scaledEquality
    (BaselKernel.kMajorMaskedKernelBaselLimitBound rate)

kMajorMaskedKernelBelowEmbeddedNat :
  ∀ {n : Nat} →
  (nPositive : suc 0 ≤ n) →
  BaselBoundary.SineProductCoefficientLimit →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (KMajor.kMajorMaskedKernel rate)
    (ConstantCancel.embeddedNat n)
kMajorMaskedKernelBelowEmbeddedNat {n} nPositive certificate =
  BishopP.≤-respʳ-≃
    (ConstantCancel.piSquareOverSixTimesStepInverseSquareIsNat nPositive)
    (kMajorMaskedKernelPiSquareBound nPositive certificate)

partitionErdosBishopKMajorPiKernelLevel : ProofLevel
partitionErdosBishopKMajorPiKernelLevel = conditional
