module DASHI.Physics.Closure.NSTriadKNFixedShiftScaleMatchedCapacityRound60Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- ROUND 60 CONTRIBUTION
--
-- Give C a concrete division-free sufficient condition that is uniform in the
-- block index.  Write T_n = C r^n.  If the literal physical quantities obey
--
--   X_n       <= K T_n,
--   A_total_n <= a T_n,
--
-- and one positive rational B_* satisfies the SINGLE coefficient inequality
--
--   a + B_* K <= r-q,
--
-- then automatically
--
--   B_* X_n <= (r-q)T_n - A_total_n
--
-- for every n.  This constructs the mature UniformFixedShiftProductCapacity
-- without any reciprocal of X_n and without a shellwise choice of B.
--
-- Thus the remaining physical C task is sharply reduced to two scale-matched
-- estimates plus one rational inequality; the all-block product capacity is a
-- theorem, not an additional hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftAggregateCriticalCapRound54Exact as Cap
import DASHI.Physics.Closure.NSTriadKNFixedShiftUniformProductCapacityRound57Exact as Capacity
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

record ScaleMatchedFixedShiftCapacityData
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    {data : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances data block) : Set where
  field
    uniformCoefficient criticalScale dataScale : ℚ

    uniformCoefficientPositive : 0ℚ < uniformCoefficient
    uniformCoefficientNonnegative : 0ℚ ≤ uniformCoefficient

    criticalIntegralNonnegative : ∀ n →
      0ℚ ≤ Owner.integralCritical (Nine.environment (balances n))

    criticalScaleBound : ∀ n →
      Owner.integralCritical (Nine.environment (balances n))
      ≤ criticalScale
        * Block.scaledTarget (Block.constant block) (Block.r block) n

    dataScaleBound : ∀ n →
      Round53.ownerAggregateDataRemainder (balances n)
      ≤ dataScale
        * Block.scaledTarget (Block.constant block) (Block.r block) n

    coefficientHeadroom :
      dataScale + uniformCoefficient * criticalScale
      ≤ Block.r block - Block.q block

open ScaleMatchedFixedShiftCapacityData public

scaleMatchedProductFitsEveryBlock :
  ∀ {balances data block identification}
    (scaleData : ScaleMatchedFixedShiftCapacityData
      {balances = balances} {data = data} {block = block} identification) →
  ∀ n →
  uniformCoefficient scaleData
    * Owner.integralCritical (Nine.environment (balances n))
  ≤ Capacity.residualCorrectionHeadroom identification n
scaleMatchedProductFitsEveryBlock
    {balances} {block = block} {identification = identification}
    scaleData n =
  let
    B = uniformCoefficient scaleData
    K = criticalScale scaleData
    a = dataScale scaleData
    X = Owner.integralCritical (Nine.environment (balances n))
    A = Round53.ownerAggregateDataRemainder (balances n)
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    gap = Block.r block - Block.q block

    scaledCritical : B * X ≤ B * (K * T)
    scaledCritical =
      let instance bNN = nonNegative (uniformCoefficientNonnegative scaleData)
      in ℚP.*-monoˡ-≤-nonNeg B (criticalScaleBound scaleData n)

    addData : A + B * X ≤ a * T + B * (K * T)
    addData = ℚP.+-mono-≤ (dataScaleBound scaleData n) scaledCritical

    regroup : a * T + B * (K * T) ≡ (a + B * K) * T
    regroup = solve (a ∷ B ∷ K ∷ T ∷ [])

    targetNN : 0ℚ ≤ T
    targetNN =
      Block.scaledTargetNonnegative
        (Block.constant block) (Block.r block)
        (Block.constantNonnegative block) (Block.rNonnegative block) n

    coefficientScaled : (a + B * K) * T ≤ gap * T
    coefficientScaled =
      let instance tNN = nonNegative targetNN
      in ℚP.*-monoʳ-≤-nonNeg T (coefficientHeadroom scaleData)

    totalFits : A + B * X ≤ gap * T
    totalFits =
      ℚP.≤-trans
        (subst (λ right → A + B * X ≤ right) regroup addData)
        coefficientScaled
  in
  Cap.removeDataRemainderFromHeadroom A B X (gap * T) totalFits

scaleMatchedUniformProductCapacity :
  ∀ {balances data block identification} →
  ScaleMatchedFixedShiftCapacityData
    {balances = balances} {data = data} {block = block} identification →
  Capacity.UniformFixedShiftProductCapacity identification
scaleMatchedUniformProductCapacity scaleData = record
  { uniformCoefficient = uniformCoefficient scaleData
  ; uniformCoefficientPositive = uniformCoefficientPositive scaleData
  ; criticalIntegralNonnegative = criticalIntegralNonnegative scaleData
  ; uniformProductFitsEveryBlock =
      scaleMatchedProductFitsEveryBlock scaleData
  }
