module DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact where

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
-- Round61's C1 surface still asked for the aggregate estimate
--
--   A_n = ownerAggregateDataRemainder_n <= a C r^n
--
-- as one opaque physical field.  That hides which owner spends the strict
-- fixed-shift gap.  The owner list is literally finite and has exactly nine
-- entries, so aggregate the nine LOCAL data-scale estimates exactly instead.
--
-- If owner i obeys
--
--   A_{i,n} <= a_i T_n,       T_n = C r^n,
--
-- then the repository's literal nine-owner list gives
--
--   A_n <= (sum_i a_i) T_n.
--
-- Hence the C2 falsifier is now the explicit local statement
--
--   a_HHg + a_HHb + a_LH + a_HL + a_CC + a_Com
--     + a_kernel + a_tail + a_boundary < r-q.
--
-- Together with ONE physical critical-scale estimate X_n <= K T_n, this file
-- constructs the exact Round61 StrictGapBlockScaleData.  No aggregate data
-- estimate is resupplied by callers.
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
import DASHI.Physics.Closure.NSTriadKNFixedShiftStrictGapCapacityRound61Exact as Strict
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

record NineOwnerLocalDataScaleBounds
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    (block : Block.RationalFixedBlockDecay) : Set where
  field
    hhGoodScale hhBadScale lhScale hlScale ccScale comScale : ℚ
    kernelScale tailScale boundaryScale : ℚ

    hhGoodDataScale : ∀ n →
      Owner.dataRemainder (Owner.hhGood (Nine.family (balances n)))
      ≤ hhGoodScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    hhBadDataScale : ∀ n →
      Owner.dataRemainder (Owner.hhBad (Nine.family (balances n)))
      ≤ hhBadScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    lhDataScale : ∀ n →
      Owner.dataRemainder (Owner.lh (Nine.family (balances n)))
      ≤ lhScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    hlDataScale : ∀ n →
      Owner.dataRemainder (Owner.hl (Nine.family (balances n)))
      ≤ hlScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    ccDataScale : ∀ n →
      Owner.dataRemainder (Owner.cc (Nine.family (balances n)))
      ≤ ccScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    comDataScale : ∀ n →
      Owner.dataRemainder (Owner.com (Nine.family (balances n)))
      ≤ comScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    kernelDataScale : ∀ n →
      Owner.dataRemainder (Owner.kernel (Nine.family (balances n)))
      ≤ kernelScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    tailDataScale : ∀ n →
      Owner.dataRemainder (Owner.tail (Nine.family (balances n)))
      ≤ tailScale * Block.scaledTarget (Block.constant block) (Block.r block) n

    boundaryDataScale : ∀ n →
      Owner.dataRemainder (Owner.boundary (Nine.family (balances n)))
      ≤ boundaryScale * Block.scaledTarget (Block.constant block) (Block.r block) n

open NineOwnerLocalDataScaleBounds public

aggregateDataScale :
  ∀ {balances block} → NineOwnerLocalDataScaleBounds {balances} block → ℚ
aggregateDataScale local =
  hhGoodScale local + hhBadScale local
  + lhScale local + hlScale local + ccScale local + comScale local
  + kernelScale local + tailScale local + boundaryScale local

aggregateDataScaleBound :
  ∀ {balances block}
    (local : NineOwnerLocalDataScaleBounds {balances} block) n →
  Round53.ownerAggregateDataRemainder (balances n)
  ≤ aggregateDataScale local
      * Block.scaledTarget (Block.constant block) (Block.r block) n
aggregateDataScaleBound {balances} {block} local n =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    family = Nine.family (balances n)

    summed :
      Owner.dataRemainder (Owner.hhGood family)
      + (Owner.dataRemainder (Owner.hhBad family)
      + (Owner.dataRemainder (Owner.lh family)
      + (Owner.dataRemainder (Owner.hl family)
      + (Owner.dataRemainder (Owner.cc family)
      + (Owner.dataRemainder (Owner.com family)
      + (Owner.dataRemainder (Owner.kernel family)
      + (Owner.dataRemainder (Owner.tail family)
      + (Owner.dataRemainder (Owner.boundary family) + 0ℚ))))))))
      ≤
      hhGoodScale local * T
      + (hhBadScale local * T
      + (lhScale local * T
      + (hlScale local * T
      + (ccScale local * T
      + (comScale local * T
      + (kernelScale local * T
      + (tailScale local * T
      + (boundaryScale local * T + 0ℚ))))))))
    summed =
      ℚP.+-mono-≤ (hhGoodDataScale local n)
      (ℚP.+-mono-≤ (hhBadDataScale local n)
      (ℚP.+-mono-≤ (lhDataScale local n)
      (ℚP.+-mono-≤ (hlDataScale local n)
      (ℚP.+-mono-≤ (ccDataScale local n)
      (ℚP.+-mono-≤ (comDataScale local n)
      (ℚP.+-mono-≤ (kernelDataScale local n)
      (ℚP.+-mono-≤ (tailDataScale local n)
      (ℚP.+-mono-≤ (boundaryDataScale local n) ℚP.≤-refl)))))))))

    rightMeaning :
      hhGoodScale local * T
      + (hhBadScale local * T
      + (lhScale local * T
      + (hlScale local * T
      + (ccScale local * T
      + (comScale local * T
      + (kernelScale local * T
      + (tailScale local * T
      + (boundaryScale local * T + 0ℚ))))))))
      ≡ aggregateDataScale local * T
    rightMeaning = solve
      ( hhGoodScale local ∷ hhBadScale local
      ∷ lhScale local ∷ hlScale local
      ∷ ccScale local ∷ comScale local
      ∷ kernelScale local ∷ tailScale local
      ∷ boundaryScale local ∷ T ∷ [])
  in
  subst
    (λ right → Round53.ownerAggregateDataRemainder (balances n) ≤ right)
    rightMeaning
    summed

record PhysicalCriticalScaleBound
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    (block : Block.RationalFixedBlockDecay) : Set where
  field
    criticalScale : ℚ
    criticalScalePositive : 0ℚ < criticalScale
    criticalIntegralNonnegative : ∀ n →
      0ℚ ≤ Owner.integralCritical (Nine.environment (balances n))
    criticalScaleBound : ∀ n →
      Owner.integralCritical (Nine.environment (balances n))
      ≤ criticalScale
        * Block.scaledTarget (Block.constant block) (Block.r block) n

open PhysicalCriticalScaleBound public

localOwnerScalesToStrictGapData :
  ∀ {balances recursionData block}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (local : NineOwnerLocalDataScaleBounds {balances} block) →
  (critical : PhysicalCriticalScaleBound {balances} block) →
  aggregateDataScale local < Block.r block - Block.q block →
  Strict.StrictGapBlockScaleData
    {balances = balances} {recursionData = recursionData}
    {block = block} identification
localOwnerScalesToStrictGapData local critical strictGap = record
  { criticalScale = criticalScale critical
  ; dataScale = aggregateDataScale local
  ; criticalScaleNonnegative = ℚP.<⇒≤ (criticalScalePositive critical)
  ; criticalIntegralNonnegative = criticalIntegralNonnegative critical
  ; criticalScaleBound = criticalScaleBound critical
  ; dataScaleBound = aggregateDataScaleBound local
  ; strictDataGap = strictGap
  }

cDataScaleIsExactSumOfNineLocalOwnerScales : Bool
cDataScaleIsExactSumOfNineLocalOwnerScales = true

cDataScaleIsExactSumOfNineLocalOwnerScalesIsTrue :
  cDataScaleIsExactSumOfNineLocalOwnerScales ≡ true
cDataScaleIsExactSumOfNineLocalOwnerScalesIsTrue = refl
