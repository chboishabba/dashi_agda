module DASHI.Physics.Closure.NSTriadKNFixedShiftUniformCorrectionCapacityRound57Exact where

-- Source: Xiaoyutao Luo, "A Beale--Kato--Majda Criterion with Optimal
-- Frequency and Temporal Localization", DOI 10.1007/s00021-019-0411-z.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftAggregateCriticalCapRound54Exact as Cap
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

shellCriticalCapacity :
  ∀ {balances data block}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification balances data block)
    (n : Nat) →
  Cap.CriticalIntegralReciprocal (Nine.environment (balances n)) → ℚ
shellCriticalCapacity {balances} {block = block} identification n reciprocal =
  Cap.criticalInverse reciprocal
    * (Headroom.fixedShiftCorrectionHeadroom block n
      - Round53.ownerAggregateDataRemainder (balances n))

record UniformFixedShiftCorrectionCapacity
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    {data : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification balances data block) : Set where
  field
    reciprocal : ∀ n → Cap.CriticalIntegralReciprocal (Nine.environment (balances n))
    uniformCap : ℚ
    uniformCapPositive : 0ℚ < uniformCap
    uniformCapBelowEveryShellCapacity : ∀ n →
      uniformCap ≤ shellCriticalCapacity identification n (reciprocal n)

open UniformFixedShiftCorrectionCapacity public

uniformSoftCoefficientFitsEveryShell :
  ∀ {balances data block}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification balances data block}
    (uniform : UniformFixedShiftCorrectionCapacity identification)
    (softCoefficient : ℚ) →
  softCoefficient ≤ uniformCap uniform →
  ∀ n → softCoefficient ≤ shellCriticalCapacity identification n (reciprocal uniform n)
uniformSoftCoefficientFitsEveryShell uniform softCoefficient softBelow n =
  ℚP.≤-trans softBelow (uniformCapBelowEveryShellCapacity uniform n)

uniformCorrectionCapacityQuantifierOrderClosed : Bool
uniformCorrectionCapacityQuantifierOrderClosed = true

uniformCorrectionCapacityQuantifierOrderClosedIsTrue :
  uniformCorrectionCapacityQuantifierOrderClosed ≡ true
uniformCorrectionCapacityQuantifierOrderClosedIsTrue = refl
