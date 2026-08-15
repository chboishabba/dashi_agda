module DASHI.Physics.Closure.NSTriadKNFixedShiftUniformProductCapacityRound57Exact where

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
-- ROUND 57 CONTRIBUTION
--
-- The shellwise reciprocal used to WRITE
--
--   B <= X^-1 (R-A)
--
-- is not needed by the fixed-shift induction.  The induction consumes only
-- the division-free product inequality
--
--   B X <= R-A.
--
-- For one global Young-soft coefficient it is therefore enough to exhibit one
-- positive rational B_* such that
--
--   B_* X_n <= R_shift(n)-A_total(n)
--
-- at every block.  This is strictly closer to the physical consumer and
-- removes the separate, currently unconstructed reciprocal-of-X leaf.  If
-- 0 <= X_n, every smaller nonnegative coefficient inherits the same capacity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

residualCorrectionHeadroom :
  ∀ {balances recursionData block}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block) →
    Nat → ℚ
residualCorrectionHeadroom {balances} {block = block} identification n =
  Headroom.fixedShiftCorrectionHeadroom block n
    - Round53.ownerAggregateDataRemainder (balances n)

record UniformFixedShiftProductCapacity
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    (identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block) : Set where
  field
    uniformCoefficient : ℚ
    uniformCoefficientPositive : 0ℚ < uniformCoefficient

    criticalIntegralNonnegative : ∀ n →
      0ℚ ≤ Owner.integralCritical (Nine.environment (balances n))

    uniformProductFitsEveryBlock : ∀ n →
      uniformCoefficient
        * Owner.integralCritical (Nine.environment (balances n))
      ≤ residualCorrectionHeadroom identification n

open UniformFixedShiftProductCapacity public

smallerNonnegativeCoefficientFitsEveryBlock :
  ∀ {balances recursionData block}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (capacity : UniformFixedShiftProductCapacity identification) →
  (coefficient : ℚ) →
  0ℚ ≤ coefficient →
  coefficient ≤ uniformCoefficient capacity →
  ∀ n →
  coefficient * Owner.integralCritical (Nine.environment (balances n))
  ≤ residualCorrectionHeadroom identification n
smallerNonnegativeCoefficientFitsEveryBlock
  {balances = balances}
  capacity coefficient coefficientNN coefficientBelow n =
  let
    critical = Owner.integralCritical (Nine.environment (balances n))
    scaled :
      coefficient * critical
      ≤ uniformCoefficient capacity * critical
    scaled =
      let instance criticalNN = nonNegative (criticalIntegralNonnegative capacity n)
      in ℚP.*-monoʳ-≤-nonNeg critical coefficientBelow
  in
  ℚP.≤-trans scaled (uniformProductFitsEveryBlock capacity n)

uniformCoefficientPlusDataFitsFullCorrectionHeadroom :
  ∀ {balances recursionData block}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (capacity : UniformFixedShiftProductCapacity identification) →
  ∀ n →
  Round53.ownerAggregateDataRemainder (balances n)
    + uniformCoefficient capacity
      * Owner.integralCritical (Nine.environment (balances n))
  ≤ Headroom.fixedShiftCorrectionHeadroom block n
uniformCoefficientPlusDataFitsFullCorrectionHeadroom
    {balances} {block = block} {identification = identification} capacity n =
  let
    A = Round53.ownerAggregateDataRemainder (balances n)
    negA = Data.Rational.Base.-_ A
    Bx = uniformCoefficient capacity
      * Owner.integralCritical (Nine.environment (balances n))
    R = Headroom.fixedShiftCorrectionHeadroom block n
    productFits : Bx ≤ R - A
    productFits = uniformProductFitsEveryBlock capacity n

    addA : A + Bx ≤ A + (R - A)
    addA = ℚP.+-monoʳ-≤ A productFits

    endpoint : A + (R - A) ≡ R
    endpoint =
      trans
        (sym (ℚP.+-assoc A R negA))
        (trans
          (cong (_+ negA) (ℚP.+-comm A R))
          (trans
            (ℚP.+-assoc R A negA)
            (trans
              (cong (R +_) (ℚP.+-inverseʳ A))
              (ℚP.+-identityʳ R))))
  in
  subst (λ right → A + Bx ≤ right) endpoint addA

uniformFixedShiftBudgetNeedsNoCriticalReciprocal : Bool
uniformFixedShiftBudgetNeedsNoCriticalReciprocal = true

uniformFixedShiftBudgetNeedsNoCriticalReciprocalIsTrue :
  uniformFixedShiftBudgetNeedsNoCriticalReciprocal ≡ true
uniformFixedShiftBudgetNeedsNoCriticalReciprocalIsTrue = refl
