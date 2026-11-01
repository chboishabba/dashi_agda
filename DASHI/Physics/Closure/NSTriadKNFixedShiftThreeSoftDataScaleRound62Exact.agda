module DASHI.Physics.Closure.NSTriadKNFixedShiftThreeSoftDataScaleRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 62 CONTRIBUTION
--
-- The actual owner constructors already force
--
--   A_HHb=A_LH=A_HL=A_CC=A_tail=A_boundary=0.
--
-- Therefore the C data-scale obstruction is not a nine-term estimate.  Once
-- the final balance uses those zero-remainder owners, only HH-good, Com and
-- kernel can spend additive fixed-shift data budget.  This module proves
--
--   A_total,n <= (a_HHg + a_Com + a_kernel) T_n
--
-- exactly from the three local bounds and the six zero identities.  Thus the
-- strict-gap falsifier becomes
--
--   a_HHg + a_Com + a_kernel < r-q.
--
-- This aligns C's additive budget with G's three Young-soft owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact as C9
import DASHI.Physics.Closure.NSTriadKNFixedShiftStrictGapCapacityRound61Exact as Strict
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

record ThreeSoftOwnerDataScaleBounds
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    (block : Block.RationalFixedBlockDecay) : Set where
  field
    hhGoodScale comScale kernelScale : ℚ

    hhBadDataZero : ∀ n →
      Owner.dataRemainder (Owner.hhBad (Nine.family (balances n))) ≡ 0ℚ
    lhDataZero : ∀ n →
      Owner.dataRemainder (Owner.lh (Nine.family (balances n))) ≡ 0ℚ
    hlDataZero : ∀ n →
      Owner.dataRemainder (Owner.hl (Nine.family (balances n))) ≡ 0ℚ
    ccDataZero : ∀ n →
      Owner.dataRemainder (Owner.cc (Nine.family (balances n))) ≡ 0ℚ
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

    kernelDataScale : ∀ n →
      Owner.dataRemainder (Owner.kernel (Nine.family (balances n)))
      ≤ kernelScale * Block.scaledTarget (Block.constant block) (Block.r block) n

open ThreeSoftOwnerDataScaleBounds public

threeSoftDataScale :
  ∀ {balances block} → ThreeSoftOwnerDataScaleBounds {balances} block → ℚ
threeSoftDataScale data =
  hhGoodScale data + comScale data + kernelScale data

threeSoftAggregateDataScaleBound :
  ∀ {balances block}
    (data : ThreeSoftOwnerDataScaleBounds {balances} block) n →
  Round53.ownerAggregateDataRemainder (balances n)
  ≤ threeSoftDataScale data
      * Block.scaledTarget (Block.constant block) (Block.r block) n
threeSoftAggregateDataScaleBound {balances} {block} data n
  rewrite hhBadDataZero data n
        | lhDataZero data n
        | hlDataZero data n
        | ccDataZero data n
        | tailDataZero data n
        | boundaryDataZero data n =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    family = Nine.family (balances n)

    summed :
      Owner.dataRemainder (Owner.hhGood family)
      + (0ℚ + (0ℚ + (0ℚ + (0ℚ
      + (Owner.dataRemainder (Owner.com family)
      + (Owner.dataRemainder (Owner.kernel family)
      + (0ℚ + (0ℚ + 0ℚ))))))))
      ≤ hhGoodScale data * T
        + (0ℚ + (0ℚ + (0ℚ + (0ℚ
        + (comScale data * T
        + (kernelScale data * T
        + (0ℚ + (0ℚ + 0ℚ))))))))
    summed =
      ℚP.+-mono-≤ (hhGoodDataScale data n)
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ (comDataScale data n)
      (ℚP.+-mono-≤ (kernelDataScale data n)
      (ℚP.+-mono-≤ ℚP.≤-refl
      (ℚP.+-mono-≤ ℚP.≤-refl ℚP.≤-refl))))))))

    rightMeaning :
      hhGoodScale data * T
        + (0ℚ + (0ℚ + (0ℚ + (0ℚ
        + (comScale data * T
        + (kernelScale data * T
        + (0ℚ + (0ℚ + 0ℚ))))))))
      ≡ threeSoftDataScale data * T
    rightMeaning = solve
      (hhGoodScale data ∷ comScale data ∷ kernelScale data ∷ T ∷ [])
  in
  subst
    (λ right → Round53.ownerAggregateDataRemainder (balances n) ≤ right)
    rightMeaning summed

threeSoftToStrictGapData :
  ∀ {balances recursionData block}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (soft : ThreeSoftOwnerDataScaleBounds {balances} block) →
  (critical : C9.PhysicalCriticalScaleBound {balances} block) →
  threeSoftDataScale soft < Block.r block - Block.q block →
  Strict.StrictGapBlockScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification
threeSoftToStrictGapData soft critical gap = record
  { criticalScale = C9.criticalScale critical
  ; dataScale = threeSoftDataScale soft
  ; criticalScaleNonnegative = ℚP.<⇒≤ (C9.criticalScalePositive critical)
  ; criticalIntegralNonnegative = C9.criticalIntegralNonnegative critical
  ; criticalScaleBound = C9.criticalScaleBound critical
  ; dataScaleBound = threeSoftAggregateDataScaleBound soft
  ; strictDataGap = gap
  }

cStrictGapReducedToThreeSoftDataOwners : Bool
cStrictGapReducedToThreeSoftDataOwners = true

cStrictGapReducedToThreeSoftDataOwnersIsTrue :
  cStrictGapReducedToThreeSoftDataOwners ≡ true
cStrictGapReducedToThreeSoftDataOwnersIsTrue = refl
