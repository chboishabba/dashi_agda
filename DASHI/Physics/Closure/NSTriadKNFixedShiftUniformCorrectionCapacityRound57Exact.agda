module DASHI.Physics.Closure.NSTriadKNFixedShiftUniformCorrectionCapacityRound57Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 57 CONTRIBUTION
--
-- Round 54 gives a shellwise additive critical-coefficient capacity
--
--   B_*(n) = X_n^{-1} (R_shift(n) - A_total(n)).
--
-- A single all-block Young allocation needs ONE positive rational B_* below
-- every shell capacity.  Merely knowing each B_*(n)>0 is insufficient.  The
-- record below is the constructive Q-form of inf_n B_*(n)>0 without inventing
-- a real infimum object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftAggregateCriticalCapRound54Exact as Cap
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

shellCriticalCapacity :
  ∀ {balances data block}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances data block)
    (n : Nat) →
  Cap.CriticalIntegralReciprocal (Nine.environment (balances n)) → ℚ
shellCriticalCapacity {balances} {block = block} identification n reciprocal =
  Cap.criticalInverse reciprocal
    * (Headroom.fixedShiftCorrectionHeadroom block n
      - Round53.ownerAggregateDataRemainder (balances n))

actualAggregateBelowShellCapacity :
  ∀ {balances data block}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances data block)
    (n : Nat)
    (reciprocal : Cap.CriticalIntegralReciprocal
      (Nine.environment (balances n))) →
  Round53.ownerAggregateCriticalCoefficient (balances n)
  ≤ shellCriticalCapacity identification n reciprocal
actualAggregateBelowShellCapacity identification n reciprocal =
  Cap.physicalAggregateCriticalCoefficientCap identification n reciprocal

record UniformFixedShiftCorrectionCapacity
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    {data : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances data block) : Set where
  field
    reciprocal : ∀ n →
      Cap.CriticalIntegralReciprocal (Nine.environment (balances n))
    uniformCap : ℚ
    uniformCapPositive : 0ℚ < uniformCap
    uniformCapBelowEveryShellCapacity : ∀ n →
      uniformCap ≤ shellCriticalCapacity identification n (reciprocal n)

open UniformFixedShiftCorrectionCapacity public

uniformSoftCoefficientFitsEveryShell :
  ∀ {balances data block}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances data block}
    (uniform : UniformFixedShiftCorrectionCapacity identification)
    (softCoefficient : ℚ) →
  softCoefficient ≤ uniformCap uniform →
  ∀ n →
  softCoefficient
  ≤ shellCriticalCapacity identification n (reciprocal uniform n)
uniformSoftCoefficientFitsEveryShell uniform softCoefficient softBelow n =
  ℚP.≤-trans softBelow (uniformCapBelowEveryShellCapacity uniform n)

uniformCorrectionCapacityQuantifierOrderClosed : Bool
uniformCorrectionCapacityQuantifierOrderClosed = true

uniformCorrectionCapacityQuantifierOrderClosedIsTrue :
  uniformCorrectionCapacityQuantifierOrderClosed ≡ true
uniformCorrectionCapacityQuantifierOrderClosedIsTrue = refl
