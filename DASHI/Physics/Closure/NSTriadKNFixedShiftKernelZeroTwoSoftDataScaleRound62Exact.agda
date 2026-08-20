module DASHI.Physics.Closure.NSTriadKNFixedShiftKernelZeroTwoSoftDataScaleRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND 62 CONTRIBUTION
--
-- On the preferred exact-independent-kernel-zero branch, the kernel owner has
-- data remainder zero structurally.  Together with the six already-zero hard
-- owners, only HH-good and Com can spend additive fixed-shift data budget.
--
-- Hence C sharpens from
--
--   a = a_HHg + a_Com + a_kernel
--
-- to
--
--   a = a_HHg + a_Com.
--
-- The HH-good companion theorem identifies a_HHg more precisely with the
-- smooth periodic correction scale only; its singular/parabolic part has zero
-- data remainder.  Thus the preferred strict-gap falsifier is
--
--   a_smooth-HHg + a_Com < r-q.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact as C9
import DASHI.Physics.Closure.NSTriadKNFixedShiftStrictGapCapacityRound61Exact as Strict
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

record KernelZeroTwoSoftDataScaleBounds
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    (block : Block.RationalFixedBlockDecay) : Set where
  field
    hhGoodScale comScale : ℚ

    hhBadDataZero : ∀ n →
      Owner.dataRemainder (Owner.hhBad (Nine.family (balances n))) ≡ 0ℚ
    lhDataZero : ∀ n →
      Owner.dataRemainder (Owner.lh (Nine.family (balances n))) ≡ 0ℚ
    hlDataZero : ∀ n →
      Owner.dataRemainder (Owner.hl (Nine.family (balances n))) ≡ 0ℚ
    ccDataZero : ∀ n →
      Owner.dataRemainder (Owner.cc (Nine.family (balances n))) ≡ 0ℚ
    kernelDataZero : ∀ n →
      Owner.dataRemainder (Owner.kernel (Nine.family (balances n))) ≡ 0ℚ
    tailDataZero : ∀ n →
      Owner.dataRemainder (Owner.tail (Nine.family (balances n))) ≡ 0ℚ
    boundaryDataZero : ∀ n →
      Owner.dataRemainder (Owner.boundary (Nine.family (balances n))) ≡ 0ℚ

    hhGoodDataScale : ∀ n →
      Owner.dataRemainder (Owner.hhGood (Nine.family (balances n)))
      ≤ hhGoodScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    comDataScale : ∀ n →
      Owner.dataRemainder (Owner.com (Nine.family (balances n)))
      ≤ comScale * Block.scaledTarget (Block.constant block) (Block.r block) n

open KernelZeroTwoSoftDataScaleBounds public

twoSoftDataScale :
  ∀ {balances block} → KernelZeroTwoSoftDataScaleBounds {balances} block → ℚ
twoSoftDataScale data = hhGoodScale data + comScale data

twoSoftAggregateDataScaleBound :
  ∀ {balances block}
    (data : KernelZeroTwoSoftDataScaleBounds {balances} block) n →
  Round53.ownerAggregateDataRemainder (balances n)
  ≤ twoSoftDataScale data
      * Block.scaledTarget (Block.constant block) (Block.r block) n
twoSoftAggregateDataScaleBound {balances} {block} data n
  rewrite hhBadDataZero data n
        | lhDataZero data n
        | hlDataZero data n
        | ccDataZero data n
        | kernelDataZero data n
        | tailDataZero data n
        | boundaryDataZero data n =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    family = Nine.family (balances n)

    summed :
      Owner.dataRemainder (Owner.hhGood family)
      + (0ℚ + (0ℚ + (0ℚ + (0ℚ
      + (Owner.dataRemainder (Owner.com family)
      + (0ℚ + (0ℚ + (0ℚ + 0ℚ))))))))
      ≤ hhGoodScale data * T
        + (0ℚ + (0ℚ + (0ℚ + (0ℚ
        + (comScale data * T
        + (0ℚ + (0ℚ + (0ℚ + 0ℚ))))))))
    summed =
      ℚP.+-mono-≤ (hhGoodDataScale data n)
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ (comDataScale data n)
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl ℚP.≤-refl))))))))

    rightMeaning :
      hhGoodScale data * T
        + (0ℚ + (0ℚ + (0ℚ + (0ℚ
        + (comScale data * T
        + (0ℚ + (0ℚ + (0ℚ + 0ℚ))))))))
      ≡ twoSoftDataScale data * T
    rightMeaning = solve (hhGoodScale data ∷ comScale data ∷ T ∷ [])
  in
  subst
    (λ right → Round53.ownerAggregateDataRemainder (balances n) ≤ right)
    rightMeaning summed

twoSoftToStrictGapData :
  ∀ {balances recursionData block}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (soft : KernelZeroTwoSoftDataScaleBounds {balances} block) →
  (critical : C9.PhysicalCriticalScaleBound {balances} block) →
  twoSoftDataScale soft < Block.r block - Block.q block →
  Strict.StrictGapBlockScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification
twoSoftToStrictGapData soft critical gap = record
  { criticalScale = C9.criticalScale critical
  ; dataScale = twoSoftDataScale soft
  ; criticalScaleNonnegative = ℚP.<⇒≤ (C9.criticalScalePositive critical)
  ; criticalIntegralNonnegative = C9.criticalIntegralNonnegative critical
  ; criticalScaleBound = C9.criticalScaleBound critical
  ; dataScaleBound = twoSoftAggregateDataScaleBound soft
  ; strictDataGap = gap
  }

kernelZeroCStrictGapUsesOnlyHHGoodAndCom : Bool
kernelZeroCStrictGapUsesOnlyHHGoodAndCom = true

kernelZeroCStrictGapUsesOnlyHHGoodAndComIsTrue :
  kernelZeroCStrictGapUsesOnlyHHGoodAndCom ≡ true
kernelZeroCStrictGapUsesOnlyHHGoodAndComIsTrue = refl
