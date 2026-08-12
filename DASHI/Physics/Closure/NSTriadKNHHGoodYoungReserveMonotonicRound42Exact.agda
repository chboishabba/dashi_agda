module DASHI.Physics.Closure.NSTriadKNHHGoodYoungReserveMonotonicRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 41 leaves the HH-good Young split epsilon as a genuine optimization
-- variable:
--
--   P <= epsilon D + (C delta E0)/(4 epsilon) X.
--
-- The viscosity tax grows with epsilon, while the critical coefficient falls.
-- This file proves the latter statement exactly on the repository's
-- `PositiveThreshold` carrier, without appealing to an external reciprocal
-- theorem.  If
--
--   0 < epsilon_1 <= epsilon_2,
--
-- then
--
--   epsilon_2^-1 <= epsilon_1^-1,
--
-- and therefore, for nonnegative effective kernel K,
--
--   B(epsilon_2) <= B(epsilon_1).
--
-- Hence after the other owner taxes are known, the optimal HH-good Young
-- choice is the largest epsilon permitted by the remaining viscosity reserve.
-- The optimizer should therefore retain epsilon until the global nine-owner
-- budget is assembled rather than fixing it upstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHGoodSquaredYoungOwnerRound41Exact as Young

positiveThresholdInverseAntitone :
  (smaller larger : Threshold.PositiveThreshold) →
  Threshold.threshold smaller ≤ Threshold.threshold larger →
  Threshold.thresholdInverse larger ≤ Threshold.thresholdInverse smaller
positiveThresholdInverseAntitone smaller larger thresholdOrder =
  let
    small = Threshold.threshold smaller
    large = Threshold.threshold larger
    smallInv = Threshold.thresholdInverse smaller
    largeInv = Threshold.thresholdInverse larger

    largeInvScaled : largeInv * small ≤ largeInv * large
    largeInvScaled =
      let instance largeInvNN = nonNegative
            (Threshold.thresholdInverseNonnegative larger)
      in ℚP.*-monoˡ-≤-nonNeg largeInv thresholdOrder

    belowOne : largeInv * small ≤ 1ℚ
    belowOne =
      subst
        (λ upper → largeInv * small ≤ upper)
        (Threshold.inverseMeaning larger)
        largeInvScaled

    scaledBySmallInv :
      smallInv * (largeInv * small) ≤ smallInv * 1ℚ
    scaledBySmallInv =
      let instance smallInvNN = nonNegative
            (Threshold.thresholdInverseNonnegative smaller)
      in ℚP.*-monoˡ-≤-nonNeg smallInv belowOne

    leftRegroup :
      smallInv * (largeInv * small)
      ≡ largeInv * (smallInv * small)
    leftRegroup = solve (smallInv ∷ largeInv ∷ small ∷ [])

    leftCancel :
      largeInv * (smallInv * small) ≡ largeInv
    leftCancel =
      trans
        (cong (largeInv *_) (Threshold.inverseMeaning smaller))
        (solve (largeInv ∷ []))

    leftMeaning :
      smallInv * (largeInv * small) ≡ largeInv
    leftMeaning = trans leftRegroup leftCancel

    rightMeaning : smallInv * 1ℚ ≡ smallInv
    rightMeaning = solve (smallInv ∷ [])
  in
  subst
    (λ lower → lower ≤ smallInv)
    leftMeaning
    (subst
      (λ upper → smallInv * (largeInv * small) ≤ upper)
      rightMeaning
      scaledBySmallInv)

youngCriticalCoefficientAntitoneInViscositySplit :
  (smaller larger : Threshold.PositiveThreshold) →
  (effectiveKernel : ℚ) →
  (parameter : Threshold.PositiveThreshold) →
  0ℚ ≤ effectiveKernel →
  Threshold.threshold smaller ≤ Threshold.threshold larger →
  Young.youngCriticalCoefficient larger effectiveKernel parameter
  ≤ Young.youngCriticalCoefficient smaller effectiveKernel parameter
youngCriticalCoefficientAntitoneInViscositySplit
    smaller larger effectiveKernel parameter effectiveNN thresholdOrder =
  let
    inverseOrder = positiveThresholdInverseAntitone
      smaller larger thresholdOrder

    kernelFactor = Young.kernelThresholdFactor effectiveKernel parameter
    kernelNN = Young.multiplyNonnegative
      effectiveNN (Threshold.thresholdNonnegative parameter)

    quarterNN : 0ℚ ≤ Young.quarter
    quarterNN = ℚP.nonNegative⁻¹ Young.quarter

    commonFactor = Young.quarter * kernelFactor
    commonNN = Young.multiplyNonnegative quarterNN kernelNN

    scaled :
      Threshold.thresholdInverse larger * commonFactor
      ≤ Threshold.thresholdInverse smaller * commonFactor
    scaled =
      let instance commonNNI = nonNegative commonNN
      in ℚP.*-monoʳ-≤-nonNeg commonFactor inverseOrder

    leftMeaning :
      Threshold.thresholdInverse larger * commonFactor
      ≡ Young.youngCriticalCoefficient larger effectiveKernel parameter
    leftMeaning = solve
      ( Threshold.thresholdInverse larger
      ∷ Young.quarter
      ∷ kernelFactor
      ∷ [])

    rightMeaning :
      Threshold.thresholdInverse smaller * commonFactor
      ≡ Young.youngCriticalCoefficient smaller effectiveKernel parameter
    rightMeaning = solve
      ( Threshold.thresholdInverse smaller
      ∷ Young.quarter
      ∷ kernelFactor
      ∷ [])
  in
  subst
    (λ lower →
      lower ≤ Young.youngCriticalCoefficient smaller effectiveKernel parameter)
    leftMeaning
    (subst
      (λ upper → Threshold.thresholdInverse larger * commonFactor ≤ upper)
      rightMeaning
      scaled)

record HHGoodReserveAdmissibleInterval
    (parameter : Threshold.PositiveThreshold)
    (effectiveKernel : ℚ) : Set where
  field
    smallerSplit largerSplit : Threshold.PositiveThreshold
    effectiveKernelNonnegative : 0ℚ ≤ effectiveKernel
    largerStillAdmissible :
      Threshold.threshold smallerSplit ≤ Threshold.threshold largerSplit

open HHGoodReserveAdmissibleInterval public

largestAdmissibleSplitHasSmallestCriticalCoefficient :
  ∀ {parameter effectiveKernel} →
  (interval : HHGoodReserveAdmissibleInterval parameter effectiveKernel) →
  Young.youngCriticalCoefficient
      (largerSplit interval) effectiveKernel parameter
  ≤ Young.youngCriticalCoefficient
      (smallerSplit interval) effectiveKernel parameter
largestAdmissibleSplitHasSmallestCriticalCoefficient
    {parameter} {effectiveKernel} interval =
  youngCriticalCoefficientAntitoneInViscositySplit
    (smallerSplit interval)
    (largerSplit interval)
    effectiveKernel
    parameter
    (effectiveKernelNonnegative interval)
    (largerStillAdmissible interval)

hhGoodYoungInverseAntitoneClosed : Bool
hhGoodYoungInverseAntitoneClosed = true

hhGoodLargestAdmissibleSplitOptimalClosed : Bool
hhGoodLargestAdmissibleSplitOptimalClosed = true

hhGoodYoungInverseAntitoneClosedIsTrue :
  hhGoodYoungInverseAntitoneClosed ≡ true
hhGoodYoungInverseAntitoneClosedIsTrue = refl

hhGoodLargestAdmissibleSplitOptimalClosedIsTrue :
  hhGoodLargestAdmissibleSplitOptimalClosed ≡ true
hhGoodLargestAdmissibleSplitOptimalClosedIsTrue = refl
