module DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorMaskedKernelExact where

------------------------------------------------------------------------
-- FINITE K-MAJOR MASKED CUBIC KERNEL
--
-- For positive n and the canonical Erdos step x_n, define for k=k'+1
--
--   q_k = D3(k*x_n)^(-1).
--
-- Mask the v-th degree-one term by the literal condition k*v <= n.  Then
--
--   sum_{k=1}^n sum_{1<=v<=n, k*v<=n} v q_k^v
--     <= (sum_{k=1}^n 1/k^2) * x_n^(-2).
--
-- No floor or division algorithm is used: each masked inner prefix is bounded
-- pointwise by the full W_n(q_k), then the cubic finite kernel and the generic
-- Nat-scale/Basel reciprocal-square theorem close the k-block.  The outer
-- common factor is pulled out by the existing finite-series owner.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselFiniteCommonFactorExact as BaselCommon
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopCubicTranslationFiniteDegreeOneKernelExact as Kernel
import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as FiniteOrder
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Foundations.BishopPositiveNatScaleReciprocalSquareExact as NatScaleReciprocal
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
open import DASHI.Physics.YangMills.CompactLieProofLevel

blockStep :
  ∀ {n} {nPositive : suc zero ≤ n} →
  Rate.ErdosStepRate n nPositive → Nat → BishopReal.ℝ
blockStep rate predecessor =
  Iterated.natScale (suc predecessor) (Rate.step rate)

blockStepPositive :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  ∀ predecessor →
  BishopReal._<_ BishopReal.0ℝ (blockStep rate predecessor)
blockStepPositive rate predecessor =
  NatScaleReciprocal.natScaleSuccessorStrictlyPositive
    (Rate.stepPositive rate) predecessor

blockRatio :
  ∀ {n} {nPositive : suc zero ≤ n} →
  (rate : Rate.ErdosStepRate n nPositive) → Nat → BishopReal.ℝ
blockRatio rate predecessor =
  Ratio.q
    (blockStep rate predecessor)
    (blockStepPositive rate predecessor)

fullBlockTerm :
  ∀ {n} {nPositive : suc zero ≤ n} →
  (rate : Rate.ErdosStepRate n nPositive) →
  Nat → Nat → BishopReal.ℝ
fullBlockTerm rate predecessor index =
  BishopReal._*_
    (Identity.natReal (suc index))
    (BishopReal.pow (blockRatio rate predecessor) (suc index))

fullBlockTermNonnegative :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  ∀ predecessor index →
  BishopReal.NonNegative (fullBlockTerm rate predecessor index)
fullBlockTermNonnegative rate predecessor index =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.pos⇒nonNeg
      (NatPositive.natRealSuccessorPositive index))
    (Iterated.powerQNonnegative
      (blockStepPositive rate predecessor)
      (suc index))

maskedBlockTerm :
  ∀ {grade n} {nPositive : suc zero ≤ grade} →
  (rate : Rate.ErdosStepRate grade nPositive) →
  Nat → Nat → BishopReal.ℝ
maskedBlockTerm {n = n} rate predecessor index
  with (suc predecessor * suc index) NatP.≤? n
... | yes _ = fullBlockTerm rate predecessor index
... | no _ = BishopReal.0ℝ

maskedTermBelowFull :
  ∀ {grade n} {nPositive : suc zero ≤ grade}
    (rate : Rate.ErdosStepRate grade nPositive) →
  ∀ predecessor index →
  BishopReal._≤_
    (maskedBlockTerm {n = n} rate predecessor index)
    (fullBlockTerm rate predecessor index)
maskedTermBelowFull {n = n} rate predecessor index
  with (suc predecessor * suc index) NatP.≤? n
... | yes _ = BishopP.≤-refl
... | no _ =
  BishopP.nonNegx⇒0≤x
    (fullBlockTermNonnegative rate predecessor index)

maskedBlockPrefix :
  ∀ {grade} {nPositive : suc zero ≤ grade} →
  (rate : Rate.ErdosStepRate grade nPositive) →
  Nat → Nat → Nat → BishopReal.ℝ
maskedBlockPrefix rate cutoff predecessor count =
  BishopSequence.SeriesOf
    (maskedBlockTerm {n = cutoff} rate predecessor)
    count

fullBlockPrefix :
  ∀ {grade} {nPositive : suc zero ≤ grade} →
  (rate : Rate.ErdosStepRate grade nPositive) →
  Nat → Nat → BishopReal.ℝ
fullBlockPrefix rate predecessor count =
  BishopSequence.SeriesOf (fullBlockTerm rate predecessor) count

maskedBlockBelowFull :
  ∀ {grade} {nPositive : suc zero ≤ grade}
    (rate : Rate.ErdosStepRate grade nPositive) →
  ∀ cutoff predecessor count →
  BishopReal._≤_
    (maskedBlockPrefix rate cutoff predecessor count)
    (fullBlockPrefix rate predecessor count)
maskedBlockBelowFull rate cutoff predecessor count =
  FiniteOrder.finitePointwiseBound count
    (λ index index<count →
      maskedTermBelowFull {n = cutoff} rate predecessor index)

fullBlockIsWeightedPartial :
  ∀ {grade} {nPositive : suc zero ≤ grade}
    (rate : Rate.ErdosStepRate grade nPositive) →
  ∀ predecessor count →
  BishopReal._≃_
    (fullBlockPrefix rate predecessor count)
    (Identity.weightedPartial (blockRatio rate predecessor) count)
fullBlockIsWeightedPartial rate predecessor zero = BishopP.≃-refl
fullBlockIsWeightedPartial rate predecessor (suc count) =
  BishopP.+-cong
    (fullBlockIsWeightedPartial rate predecessor count)
    BishopP.≃-refl

maskedBlockBelowWeightedPartial :
  ∀ {grade} {nPositive : suc zero ≤ grade}
    (rate : Rate.ErdosStepRate grade nPositive) →
  ∀ cutoff predecessor count →
  BishopReal._≤_
    (maskedBlockPrefix rate cutoff predecessor count)
    (Identity.weightedPartial (blockRatio rate predecessor) count)
maskedBlockBelowWeightedPartial rate cutoff predecessor count =
  BishopP.≤-respʳ-≃
    (fullBlockIsWeightedPartial rate predecessor count)
    (maskedBlockBelowFull rate cutoff predecessor count)

blockBaselBound :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  ∀ predecessor →
  BishopReal._<_
    (maskedBlockPrefix rate n predecessor n)
    (BishopReal._*_
      (Basel.baselTerm predecessor)
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
blockBaselBound {n} rate predecessor =
  let
    stepPositive = blockStepPositive rate predecessor
    fullKernel = Kernel.cubicFiniteDegreeOneKernel stepPositive n
    normalizedKernel =
      BishopP.<-respʳ-≃
        (NatScaleReciprocal.natScaleSuccessorReciprocalSquare
          (Rate.stepPositive rate) predecessor)
        fullKernel
  in
  BishopP.≤-<-trans
    (maskedBlockBelowWeightedPartial rate n predecessor n)
    normalizedKernel

kMajorMaskedKernel :
  ∀ {n} {nPositive : suc zero ≤ n} →
  Rate.ErdosStepRate n nPositive → BishopReal.ℝ
kMajorMaskedKernel {n} rate =
  BishopSequence.SeriesOf
    (λ predecessor → maskedBlockPrefix rate n predecessor n)
    n

scaledBaselTerms :
  ∀ {n} {nPositive : suc zero ≤ n} →
  Rate.ErdosStepRate n nPositive → Nat → BishopReal.ℝ
scaledBaselTerms rate predecessor =
  BishopReal._*_
    (Basel.baselTerm predecessor)
    (Reciprocal.inverseSquare
      (Rate.step rate)
      (Reciprocal.xNonzero (Rate.stepPositive rate)))

kMajorMaskedKernelBelowScaledBasel :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  BishopReal._≤_
    (kMajorMaskedKernel rate)
    (BishopSequence.SeriesOf (scaledBaselTerms rate) n)
kMajorMaskedKernelBelowScaledBasel {n} rate =
  FiniteOrder.finitePointwiseBound n
    (λ predecessor predecessor<n →
      BishopP.<⇒≤ (blockBaselBound rate predecessor))

scaledBaselSeriesIsCommonFactor :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  BishopReal._≃_
    (BishopSequence.SeriesOf (scaledBaselTerms rate) n)
    (BishopReal._*_
      (BishopSequence.SeriesOf Basel.baselTerm n)
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
scaledBaselSeriesIsCommonFactor {n} rate =
  BishopP.≃-trans
    (BishopP.≃-symm
      (FinSum.finSumIsSeriesOf (scaledBaselTerms rate) n))
    (BaselCommon.scaledBaselFinitePrefixCommonFactor
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate)))
      n)

kMajorMaskedKernelBaselPrefixBound :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  BishopReal._≤_
    (kMajorMaskedKernel rate)
    (BishopReal._*_
      (BishopSequence.SeriesOf Basel.baselTerm n)
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
kMajorMaskedKernelBaselPrefixBound rate =
  BishopP.≤-respʳ-≃
    (scaledBaselSeriesIsCommonFactor rate)
    (kMajorMaskedKernelBelowScaledBasel rate)

canonicalKMajorMaskedKernelBaselPrefixBound :
  ∀ {n} →
  (nPositive : suc zero ≤ n) →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (kMajorMaskedKernel rate)
    (BishopReal._*_
      (BishopSequence.SeriesOf Basel.baselTerm n)
      (Reciprocal.inverseSquare
        (Rate.step rate)
        (Reciprocal.xNonzero (Rate.stepPositive rate))))
canonicalKMajorMaskedKernelBaselPrefixBound {n} nPositive =
  kMajorMaskedKernelBaselPrefixBound
    (Rate.canonicalErdosStepRate n nPositive)

partitionErdosBishopKMajorMaskedKernelLevel : ProofLevel
partitionErdosBishopKMajorMaskedKernelLevel = machineChecked
