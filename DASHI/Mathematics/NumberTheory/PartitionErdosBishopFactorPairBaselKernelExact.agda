module DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairBaselKernelExact where

------------------------------------------------------------------------
-- LITERAL BASEL-TERM FACTOR KERNEL
--
-- Replace the embedded-Nat reciprocal square in the normalized factor kernel
-- by the exact Basel sequence term at predecessor k-1.  The common x_n^-2
-- factor remains untouched for outer finite summation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatBasel
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact as FactorResidual
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairNormalizedKernelExact as Normalized
open import DASHI.Physics.YangMills.CompactLieProofLevel

factorPairBaselFiniteDegreeOneKernel :
  ∀ {n r : Nat} {nPositive : suc 0 ≤ n} →
  (rate : Rate.ErdosStepRate n nPositive) →
  (pair : Factor.PositiveFactorPair r) →
  ∀ count →
  let
    step = FactorResidual.factorStep rate pair
    stepPositive = FactorResidual.factorStepPositive rate pair
  in
  BishopReal._<_
    (Identity.weightedPartial (Ratio.q step stepPositive) count)
    (BishopReal._*_
      (Basel.baselTerm (Factor.predecessor pair))
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
factorPairBaselFiniteDegreeOneKernel rate pair count =
  BishopP.<-respʳ-≃
    (BishopP.*-congʳ
      (NatBasel.natRealSuccessorInverseSquareIsBaselTerm
        (Factor.predecessor pair)))
    (Normalized.factorPairNormalizedFiniteDegreeOneKernel
      rate pair count)

canonicalFactorPairBaselFiniteDegreeOneKernel :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  (pair : Factor.PositiveFactorPair r) →
  ∀ count →
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    step = FactorResidual.factorStep rate pair
    stepPositive = FactorResidual.factorStepPositive rate pair
  in
  BishopReal._<_
    (Identity.weightedPartial (Ratio.q step stepPositive) count)
    (BishopReal._*_
      (Basel.baselTerm (Factor.predecessor pair))
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
canonicalFactorPairBaselFiniteDegreeOneKernel {n} nPositive pair count =
  factorPairBaselFiniteDegreeOneKernel
    (Rate.canonicalErdosStepRate n nPositive)
    pair count

partitionErdosBishopFactorPairBaselKernelLevel : ProofLevel
partitionErdosBishopFactorPairBaselKernelLevel = machineChecked
