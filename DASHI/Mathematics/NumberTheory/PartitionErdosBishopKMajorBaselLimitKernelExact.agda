module DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorBaselLimitKernelExact where

------------------------------------------------------------------------
-- K-MAJOR CUBIC KERNEL <= BASEL LIMIT * x_n^(-2)
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselFinitePrefixBelowLimitExact as BaselPrefix
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorMaskedKernelExact as KMajor
open import DASHI.Physics.YangMills.CompactLieProofLevel

kMajorMaskedKernelBaselLimitBound :
  ∀ {n} {nPositive : suc 0 ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  BishopReal._≤_
    (KMajor.kMajorMaskedKernel rate)
    (BishopReal._*_
      Basel.baselLimit
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
kMajorMaskedKernelBaselLimitBound {n} rate =
  let
    factor =
      Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))
    factorNN =
      BishopP.pos⇒nonNeg
        (Reciprocal.inverseSquarePositive
          (Reciprocal.xNonzero (Rate.stepPositive rate))
          (Rate.stepPositive rate))
    scaledPrefixBelowLimit =
      BishopP.*-monoʳ-≤-nonNeg
        (BaselPrefix.baselFinitePrefixBelowLimit n)
        factorNN
  in
  BishopP.≤-trans
    (KMajor.kMajorMaskedKernelBaselPrefixBound rate)
    scaledPrefixBelowLimit

canonicalKMajorMaskedKernelBaselLimitBound :
  ∀ {n} →
  (nPositive : suc 0 ≤ n) →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (KMajor.kMajorMaskedKernel rate)
    (BishopReal._*_
      Basel.baselLimit
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
canonicalKMajorMaskedKernelBaselLimitBound {n} nPositive =
  kMajorMaskedKernelBaselLimitBound
    (Rate.canonicalErdosStepRate n nPositive)

partitionErdosBishopKMajorBaselLimitKernelLevel : ProofLevel
partitionErdosBishopKMajorBaselLimitKernelLevel = machineChecked
