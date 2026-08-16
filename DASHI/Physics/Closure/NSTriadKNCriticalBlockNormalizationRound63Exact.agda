module DASHI.Physics.Closure.NSTriadKNCriticalBlockNormalizationRound63Exact where

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
-- ROUND 63 / C0
--
-- Separate the geometric block scale from the genuinely analytic uniformity
-- problem.  The fixed-block target is already definitionally
--
--     T_n = C r^n.
--
-- A physical producer should therefore first exhibit a dimensionless block
-- functional Xi_n with
--
--     X_n <= T_n Xi_n,
--
-- and only then prove the scale-independent estimate Xi_n <= K.  The theorem
-- below composes exactly those two facts into the mature C1 statement
--
--     X_n <= K C r^n.
--
-- IMPORTANT: the existing owner language does NOT construct Xi_n.  Its
-- `TaxEnvironment.integralCritical` field is an unconstrained rational scalar.
-- This module therefore does not manufacture Xi_n by division or use final
-- correction headroom.  It exposes the missing producer in the strongest
-- useful factorized form.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

record CriticalBlockNormalization
    (balances : Nat → Nine.NineOwnerCriticalBalance)
    (block : Block.RationalFixedBlockDecay) : Set where
  field
    normalizedCritical : Nat → ℚ
    normalizedCriticalNonnegative : ∀ n → 0ℚ ≤ normalizedCritical n

    criticalBelowTargetTimesNormalized : ∀ n →
      Owner.integralCritical (Nine.environment (balances n))
      ≤ Block.scaledTarget (Block.constant block) (Block.r block) n
        * normalizedCritical n

open CriticalBlockNormalization public

record UniformNormalizedCriticalBound
    {balances : Nat → Nine.NineOwnerCriticalBalance}
    {block : Block.RationalFixedBlockDecay}
    (normalization : CriticalBlockNormalization balances block) : Set where
  field
    uniformCriticalConstant : ℚ
    uniformCriticalConstantNonnegative : 0ℚ ≤ uniformCriticalConstant
    normalizedCriticalBelowUniform : ∀ n →
      normalizedCritical normalization n ≤ uniformCriticalConstant

open UniformNormalizedCriticalBound public

normalizedUniformityImpliesC1 :
  ∀ {balances block}
    {normalization : CriticalBlockNormalization balances block} →
  (uniform : UniformNormalizedCriticalBound normalization) →
  ∀ n →
  Owner.integralCritical (Nine.environment (balances n))
  ≤ uniformCriticalConstant uniform
      * Block.scaledTarget (Block.constant block) (Block.r block) n
normalizedUniformityImpliesC1
    {block = block} {normalization = normalization} uniform n =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    Xi = normalizedCritical normalization n
    K = uniformCriticalConstant uniform

    targetNN : 0ℚ ≤ T
    targetNN =
      Block.scaledTargetNonnegative
        (Block.constant block) (Block.r block)
        (Block.constantNonnegative block) (Block.rNonnegative block) n

    normalizedStep : T * Xi ≤ T * K
    normalizedStep =
      let instance tNN = nonNegative targetNN
      in ℚP.*-monoˡ-≤-nonNeg T (normalizedCriticalBelowUniform uniform n)

    productCommutes : T * K ≡ K * T
    productCommutes = ℚP.*-comm T K
  in
  ℚP.≤-trans
    (criticalBelowTargetTimesNormalized normalization n)
    (subst (λ upper → T * Xi ≤ upper) productCommutes normalizedStep)

-- The owner environment itself contains no block index, no C, no r, and no
-- normalization map.  This constructor/equality pair records the exact source
-- of the C0 obligation: arbitrary critical scalars inhabit the owner language.
arbitraryCriticalEnvironment : ℚ → ℚ → Owner.TaxEnvironment
arbitraryCriticalEnvironment dissipation critical =
  Owner.tax-environment dissipation critical

arbitraryCriticalEnvironmentMeaning :
  ∀ dissipation critical →
  Owner.integralCritical (arbitraryCriticalEnvironment dissipation critical)
  ≡ critical
arbitraryCriticalEnvironmentMeaning dissipation critical = refl

c0SeparatesGeometricScaleFromUniformNormalizedBound : Bool
c0SeparatesGeometricScaleFromUniformNormalizedBound = true

c0OwnerEnvironmentDoesNotConstructNormalization : Bool
c0OwnerEnvironmentDoesNotConstructNormalization = true

c0SeparatesGeometricScaleFromUniformNormalizedBoundIsTrue :
  c0SeparatesGeometricScaleFromUniformNormalizedBound ≡ true
c0SeparatesGeometricScaleFromUniformNormalizedBoundIsTrue = refl

c0OwnerEnvironmentDoesNotConstructNormalizationIsTrue :
  c0OwnerEnvironmentDoesNotConstructNormalization ≡ true
c0OwnerEnvironmentDoesNotConstructNormalizationIsTrue = refl
