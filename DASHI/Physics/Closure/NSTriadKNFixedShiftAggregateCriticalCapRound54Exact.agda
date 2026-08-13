module DASHI.Physics.Closure.NSTriadKNFixedShiftAggregateCriticalCapRound54Exact where

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
-- DASHI CONTRIBUTION
--
-- Round 54 turns the exact additive fixed-shift headroom into the actual
-- aggregate B-budget.  From
--
--   A_total + B_total X <= R_shift
--
-- it first derives, without division,
--
--   B_total X <= R_shift - A_total.
--
-- If the selected critical integral X is positive with an explicitly supplied
-- reciprocal, this gives the sharp shellwise coefficient cap
--
--   B_total <= X^{-1} (R_shift - A_total).
--
-- This is the quantity that must be used for JOINT allocation of Young-soft
-- owners.  There is no mathematical basis for inventing separate Com/kernel/
-- HH-good recursion floors once Round 53 has shown only their aggregate enters
-- the correction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom

removeDataRemainderFromHeadroom :
  ∀ A B X R →
  A + B * X ≤ R →
  B * X ≤ R - A
removeDataRemainderFromHeadroom A B X R totalBound =
  let
    shifted :
      (- A) + (A + B * X) ≤ (- A) + R
    shifted = ℚP.+-monoʳ-≤ (- A) totalBound

    leftMeaning : (- A) + (A + B * X) ≡ B * X
    leftMeaning = solve (A ∷ B ∷ X ∷ [])

    rightMeaning : (- A) + R ≡ R - A
    rightMeaning = solve (A ∷ R ∷ [])
  in
  subst
    (λ left → left ≤ R - A)
    leftMeaning
    (subst
      (λ right → (- A) + (A + B * X) ≤ right)
      rightMeaning
      shifted)

record CriticalIntegralReciprocal
    (environment : Owner.TaxEnvironment) : Set where
  field
    criticalInverse : ℚ
    criticalInverseNonnegative : 0ℚ ≤ criticalInverse
    inverseMeaning :
      criticalInverse * Owner.integralCritical environment ≡ 1ℚ

open CriticalIntegralReciprocal public

inverseTimesCriticalProduct :
  ∀ {environment}
    (reciprocal : CriticalIntegralReciprocal environment)
    (coefficient : ℚ) →
  criticalInverse reciprocal
    * (coefficient * Owner.integralCritical environment)
  ≡ coefficient
inverseTimesCriticalProduct {environment} reciprocal coefficient =
  let
    regroup :
      criticalInverse reciprocal
        * (coefficient * Owner.integralCritical environment)
      ≡ coefficient
        * (criticalInverse reciprocal * Owner.integralCritical environment)
    regroup = solve
      ( criticalInverse reciprocal
      ∷ coefficient
      ∷ Owner.integralCritical environment
      ∷ [])

    cancel :
      coefficient
        * (criticalInverse reciprocal * Owner.integralCritical environment)
      ≡ coefficient * 1ℚ
    cancel = cong (coefficient *_) (inverseMeaning reciprocal)
  in
  trans regroup (trans cancel (ℚP.*-identityʳ coefficient))

ownerAggregateCriticalTimesIntegralBelowResidualHeadroom :
  ∀ {balances data block} →
  (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
    balances data block) →
  (n : Nat) →
  Round53.ownerAggregateCriticalCoefficient (balances n)
    * Owner.integralCritical (Nine.environment (balances n))
  ≤ Headroom.fixedShiftCorrectionHeadroom block n
      - Round53.ownerAggregateDataRemainder (balances n)
ownerAggregateCriticalTimesIntegralBelowResidualHeadroom
    {balances} {block = block} identification n =
  removeDataRemainderFromHeadroom
    (Round53.ownerAggregateDataRemainder (balances n))
    (Round53.ownerAggregateCriticalCoefficient (balances n))
    (Owner.integralCritical (Nine.environment (balances n)))
    (Headroom.fixedShiftCorrectionHeadroom block n)
    (Headroom.physicalOwnerAggregateBelowFixedShiftHeadroom identification n)

physicalAggregateCriticalCoefficientCap :
  ∀ {balances data block} →
  (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
    balances data block) →
  (n : Nat) →
  (reciprocal : CriticalIntegralReciprocal
    (Nine.environment (balances n))) →
  Round53.ownerAggregateCriticalCoefficient (balances n)
  ≤ criticalInverse reciprocal
      * (Headroom.fixedShiftCorrectionHeadroom block n
          - Round53.ownerAggregateDataRemainder (balances n))
physicalAggregateCriticalCoefficientCap
    {balances} {block = block} identification n reciprocal =
  let
    residualBound =
      ownerAggregateCriticalTimesIntegralBelowResidualHeadroom
        identification n

    scaled :
      criticalInverse reciprocal
        * (Round53.ownerAggregateCriticalCoefficient (balances n)
          * Owner.integralCritical (Nine.environment (balances n)))
      ≤ criticalInverse reciprocal
        * (Headroom.fixedShiftCorrectionHeadroom block n
          - Round53.ownerAggregateDataRemainder (balances n))
    scaled =
      let instance inverseNNI = nonNegative (criticalInverseNonnegative reciprocal)
      in ℚP.*-monoˡ-≤-nonNeg (criticalInverse reciprocal) residualBound
  in
  subst
    (λ left →
      left
      ≤ criticalInverse reciprocal
        * (Headroom.fixedShiftCorrectionHeadroom block n
          - Round53.ownerAggregateDataRemainder (balances n)))
    (inverseTimesCriticalProduct reciprocal
      (Round53.ownerAggregateCriticalCoefficient (balances n)))
    scaled

aggregateBCapIsCorrectionHeadroomNotRecursionCoefficient : Bool
aggregateBCapIsCorrectionHeadroomNotRecursionCoefficient = true

jointSoftAllocationRequiredAfterAggregateCap : Bool
jointSoftAllocationRequiredAfterAggregateCap = true

criticalIntegralReciprocalConstructedForLiteralShells : Bool
criticalIntegralReciprocalConstructedForLiteralShells = false

aggregateBCapIsCorrectionHeadroomNotRecursionCoefficientIsTrue :
  aggregateBCapIsCorrectionHeadroomNotRecursionCoefficient ≡ true
aggregateBCapIsCorrectionHeadroomNotRecursionCoefficientIsTrue = refl

jointSoftAllocationRequiredAfterAggregateCapIsTrue :
  jointSoftAllocationRequiredAfterAggregateCap ≡ true
jointSoftAllocationRequiredAfterAggregateCapIsTrue = refl
