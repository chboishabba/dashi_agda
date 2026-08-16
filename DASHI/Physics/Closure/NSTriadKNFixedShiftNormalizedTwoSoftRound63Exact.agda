module DASHI.Physics.Closure.NSTriadKNFixedShiftNormalizedTwoSoftRound63Exact where

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
-- ROUND 63 C-DATA CONTRIBUTION
--
-- On the preferred independent-kernel-zero branch only HH-good's smooth
-- remainder and Com survive.  The final fixed-shift gate consumes their SUM,
-- so there is no mathematical need to optimize two constants independently.
--
-- For positive block target T_n=C r^n construct exactly
--
--   Xi_soft,n := (A_HHg,n + A_Com,n) / T_n.
--
-- Then
--
--   A_HHg,n + A_Com,n = T_n Xi_soft,n
--
-- definitionally up to exact rational field algebra.  Hence a single uniform
-- bound Xi_soft,n <= a_soft gives the aggregate nine-owner data estimate once
-- the seven structural zero remainders are supplied.  The remaining C-data
-- theorem is therefore one dimensionless uniform bound plus a_soft<r-q.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; NonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftStrictGapCapacityRound61Exact as Strict
import DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact as C9
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNCriticalScaleNormalizedBlockRound63Exact as C0

hhGoodDataValue :
  (balances : Nat → Nine.NineOwnerCriticalBalance) → Nat → ℚ
hhGoodDataValue balances n =
  Owner.dataRemainder (Owner.hhGood (Nine.family (balances n)))

comDataValue :
  (balances : Nat → Nine.NineOwnerCriticalBalance) → Nat → ℚ
comDataValue balances n =
  Owner.dataRemainder (Owner.com (Nine.family (balances n)))

twoSoftDataValue :
  (balances : Nat → Nine.NineOwnerCriticalBalance) → Nat → ℚ
twoSoftDataValue balances n = hhGoodDataValue balances n + comDataValue balances n

normalizedTwoSoftData :
  (balances : Nat → Nine.NineOwnerCriticalBalance) →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : C0.PositiveCriticalBlockScale block) →
  Nat → ℚ
normalizedTwoSoftData balances block positiveScale n =
  twoSoftDataValue balances n
  * C0.positiveReciprocal
      (C0.blockTarget block n)
      (C0.blockTargetPositive block positiveScale n)

twoSoftFactorization :
  (balances : Nat → Nine.NineOwnerCriticalBalance) →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : C0.PositiveCriticalBlockScale block) →
  (n : Nat) →
  C0.blockTarget block n * normalizedTwoSoftData balances block positiveScale n
  ≡ twoSoftDataValue balances n
twoSoftFactorization balances block positiveScale n =
  let
    target = C0.blockTarget block n
    targetPositive = C0.blockTargetPositive block positiveScale n
    reciprocal = C0.positiveReciprocal target targetPositive
    value = twoSoftDataValue balances n
    regroup : target * (value * reciprocal) ≡ value * (target * reciprocal)
    regroup = solve (target ∷ value ∷ reciprocal ∷ [])
  in
  trans regroup
    (trans
      (cong (value *_)
        (C0.positiveReciprocalRightInverse target targetPositive))
      (solve (value ∷ [])))

normalizedTwoSoftBoundImpliesScale :
  (balances : Nat → Nine.NineOwnerCriticalBalance) →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : C0.PositiveCriticalBlockScale block) →
  (aSoft : ℚ) →
  ((n : Nat) → normalizedTwoSoftData balances block positiveScale n ≤ aSoft) →
  (n : Nat) →
  twoSoftDataValue balances n ≤ aSoft * C0.blockTarget block n
normalizedTwoSoftBoundImpliesScale balances block positiveScale aSoft uniform n =
  let
    target = C0.blockTarget block n
    targetNN : 0ℚ ≤ target
    targetNN = ℚP.<⇒≤ (C0.blockTargetPositive block positiveScale n)
    instance targetIsNN : NonNegative target
    targetIsNN = ℚ.nonNegative targetNN

    scaled :
      target * normalizedTwoSoftData balances block positiveScale n
      ≤ target * aSoft
    scaled = ℚP.*-monoˡ-≤-nonNeg target (uniform n)

    leftMeaning = twoSoftFactorization balances block positiveScale n
    rightMeaning : target * aSoft ≡ aSoft * target
    rightMeaning = solve (target ∷ aSoft ∷ [])
  in
  subst
    (λ left → left ≤ aSoft * target)
    leftMeaning
    (subst
      (λ right →
        target * normalizedTwoSoftData balances block positiveScale n ≤ right)
      rightMeaning scaled)

record KernelZeroSevenRemainders
    (balances : Nat → Nine.NineOwnerCriticalBalance) : Set where
  field
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

open KernelZeroSevenRemainders public

aggregateRemainderIsTwoSoft :
  (balances : Nat → Nine.NineOwnerCriticalBalance) →
  KernelZeroSevenRemainders balances →
  (n : Nat) →
  Round53.ownerAggregateDataRemainder (balances n)
  ≡ twoSoftDataValue balances n
aggregateRemainderIsTwoSoft balances zeros n
  rewrite hhBadDataZero zeros n
        | lhDataZero zeros n
        | hlDataZero zeros n
        | ccDataZero zeros n
        | kernelDataZero zeros n
        | tailDataZero zeros n
        | boundaryDataZero zeros n =
  solve
    ( hhGoodDataValue balances n
    ∷ comDataValue balances n
    ∷ [])

normalizedTwoSoftToStrictGapData :
  {balances : Nat → Nine.NineOwnerCriticalBalance} →
  {recursionData : Fixed.FixedShiftRecursionPhysicalData} →
  {block : Block.RationalFixedBlockDecay} →
  {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
    balances recursionData block} →
  (positiveScale : C0.PositiveCriticalBlockScale block) →
  (zeros : KernelZeroSevenRemainders balances) →
  (critical : C9.PhysicalCriticalScaleBound {balances} block) →
  (aSoft : ℚ) →
  ((n : Nat) → normalizedTwoSoftData balances block positiveScale n ≤ aSoft) →
  aSoft < Block.r block - Block.q block →
  Strict.StrictGapBlockScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification
normalizedTwoSoftToStrictGapData
    {balances} {block = block}
    positiveScale zeros critical aSoft uniform strictGap = record
  { criticalScale = C9.criticalScale critical
  ; dataScale = aSoft
  ; criticalScaleNonnegative = ℚP.<⇒≤ (C9.criticalScalePositive critical)
  ; criticalIntegralNonnegative = C9.criticalIntegralNonnegative critical
  ; criticalScaleBound = C9.criticalScaleBound critical
  ; dataScaleBound = λ n →
      subst
        (λ left → left ≤ aSoft * C0.blockTarget block n)
        (sym (aggregateRemainderIsTwoSoft balances zeros n))
        (normalizedTwoSoftBoundImpliesScale
          balances block positiveScale aSoft uniform n)
  ; strictDataGap = strictGap
  }

cDataReducedToOneNormalizedTwoSoftFunctional : Bool
cDataReducedToOneNormalizedTwoSoftFunctional = true

cDataReducedToOneNormalizedTwoSoftFunctionalIsTrue :
  cDataReducedToOneNormalizedTwoSoftFunctional ≡ true
cDataReducedToOneNormalizedTwoSoftFunctionalIsTrue = refl
