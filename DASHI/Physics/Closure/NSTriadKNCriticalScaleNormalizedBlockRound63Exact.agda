module DASHI.Physics.Closure.NSTriadKNCriticalScaleNormalizedBlockRound63Exact where

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
-- ROUND 63 C0 CONTRIBUTION
--
-- The Round62 critical-scale target was written
--
--   X_n <= K * (C r^n).
--
-- The geometric factor C r^n is already the literal fixed-block target.  This
-- file separates that definitional scaling from the genuinely analytic
-- uniformity question by constructing, whenever C>0 and r>0, the exact
-- dimensionless rational block functional
--
--   Xi_n := X_n / (C r^n)
--
-- using the positive rational reciprocal.  No target estimate is supplied as a
-- record field.  Exact rational algebra proves
--
--   X_n = (C r^n) Xi_n.
--
-- Consequently C1 is equivalent to the scale-free uniform statement
--
--   Xi_n <= K.
--
-- This module imports no final correction capacity or Young allocation, so the
-- Round62 anti-circularity boundary is preserved definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; 1/_; Positive; NonNegative; NonZero)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

blockTarget : Block.RationalFixedBlockDecay → Nat → ℚ
blockTarget block n =
  Block.scaledTarget (Block.constant block) (Block.r block) n

criticalValue :
  (balances : Nat → Nine.NineOwnerCriticalBalance) → Nat → ℚ
criticalValue balances n =
  Owner.integralCritical (Nine.environment (balances n))

record PositiveCriticalBlockScale (block : Block.RationalFixedBlockDecay) : Set where
  constructor positive-critical-block-scale
  field
    constantPositive : 0ℚ < Block.constant block
    ratioPositive : 0ℚ < Block.r block

open PositiveCriticalBlockScale public

powerPositive :
  (ratio : ℚ) →
  0ℚ < ratio →
  (n : Nat) →
  0ℚ < Block.power ratio n
powerPositive ratio ratioPositive zero = ℚP.positive⁻¹ 1ℚ
powerPositive ratio ratioPositive (suc n) =
  let
    instance
      ratioIsPositive : Positive ratio
      ratioIsPositive = ℚ.positive ratioPositive

      tailIsPositive : Positive (Block.power ratio n)
      tailIsPositive = ℚ.positive (powerPositive ratio ratioPositive n)

      productIsPositive : Positive (ratio * Block.power ratio n)
      productIsPositive = ℚP.pos*pos⇒pos ratio (Block.power ratio n)
  in
  ℚP.positive⁻¹ (ratio * Block.power ratio n)

blockTargetPositive :
  (block : Block.RationalFixedBlockDecay) →
  PositiveCriticalBlockScale block →
  (n : Nat) →
  0ℚ < blockTarget block n
blockTargetPositive block positiveScale n =
  let
    constant = Block.constant block
    ratio = Block.r block
    tail = Block.power ratio n

    instance
      constantIsPositive : Positive constant
      constantIsPositive = ℚ.positive (constantPositive positiveScale)

      tailIsPositive : Positive tail
      tailIsPositive = ℚ.positive (powerPositive ratio (ratioPositive positiveScale) n)

      targetIsPositive : Positive (constant * tail)
      targetIsPositive = ℚP.pos*pos⇒pos constant tail
  in
  ℚP.positive⁻¹ (blockTarget block n)

positiveReciprocal :
  (denominator : ℚ) →
  0ℚ < denominator →
  ℚ
positiveReciprocal denominator denominatorPositive =
  let
    instance
      denominatorIsPositive : Positive denominator
      denominatorIsPositive = ℚ.positive denominatorPositive

      denominatorIsNonzero : NonZero denominator
      denominatorIsNonzero = ℚP.pos⇒nonZero denominator
  in
  1/ denominator

positiveReciprocalRightInverse :
  (denominator : ℚ) →
  (denominatorPositive : 0ℚ < denominator) →
  denominator * positiveReciprocal denominator denominatorPositive ≡ 1ℚ
positiveReciprocalRightInverse denominator denominatorPositive =
  let
    instance
      denominatorIsPositive : Positive denominator
      denominatorIsPositive = ℚ.positive denominatorPositive

      denominatorIsNonzero : NonZero denominator
      denominatorIsNonzero = ℚP.pos⇒nonZero denominator
  in
  ℚP.*-inverseʳ denominator

normalizedCritical :
  (balances : Nat → Nine.NineOwnerCriticalBalance) →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : PositiveCriticalBlockScale block) →
  Nat → ℚ
normalizedCritical balances block positiveScale n =
  criticalValue balances n
  * positiveReciprocal
      (blockTarget block n)
      (blockTargetPositive block positiveScale n)

criticalFactorization :
  (balances : Nat → Nine.NineOwnerCriticalBalance) →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : PositiveCriticalBlockScale block) →
  (n : Nat) →
  blockTarget block n * normalizedCritical balances block positiveScale n
  ≡ criticalValue balances n
criticalFactorization balances block positiveScale n =
  let
    target = blockTarget block n
    targetPositive = blockTargetPositive block positiveScale n
    reciprocal = positiveReciprocal target targetPositive
    inverse = positiveReciprocalRightInverse target targetPositive
    x = criticalValue balances n

    reassociate : target * (x * reciprocal) ≡ x * (target * reciprocal)
    reassociate = solve (target ∷ x ∷ reciprocal ∷ [])
  in
  trans
    reassociate
    (trans
      (cong (x *_) inverse)
      (solve (x ∷ [])))

normalizedBoundImpliesCriticalScale :
  (balances : Nat → Nine.NineOwnerCriticalBalance) →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : PositiveCriticalBlockScale block) →
  (K : ℚ) →
  ((n : Nat) → normalizedCritical balances block positiveScale n ≤ K) →
  (n : Nat) →
  criticalValue balances n ≤ K * blockTarget block n
normalizedBoundImpliesCriticalScale balances block positiveScale K normalizedBound n =
  let
    target = blockTarget block n
    targetNN : 0ℚ ≤ target
    targetNN = ℚP.<⇒≤ (blockTargetPositive block positiveScale n)

    instance
      targetIsNonnegative : NonNegative target
      targetIsNonnegative = ℚ.nonNegative targetNN

    scaled :
      target * normalizedCritical balances block positiveScale n
      ≤ target * K
    scaled = ℚP.*-monoˡ-≤-nonNeg target (normalizedBound n)

    leftMeaning :
      target * normalizedCritical balances block positiveScale n
      ≡ criticalValue balances n
    leftMeaning = criticalFactorization balances block positiveScale n

    rightMeaning : target * K ≡ K * target
    rightMeaning = solve (target ∷ K ∷ [])
  in
  subst
    (λ left → left ≤ K * target)
    leftMeaning
    (subst
      (λ right → target * normalizedCritical balances block positiveScale n ≤ right)
      rightMeaning
      scaled)

criticalScaleBoundImpliesNormalizedBound :
  (balances : Nat → Nine.NineOwnerCriticalBalance) →
  (block : Block.RationalFixedBlockDecay) →
  (positiveScale : PositiveCriticalBlockScale block) →
  (K : ℚ) →
  ((n : Nat) → criticalValue balances n ≤ K * blockTarget block n) →
  (n : Nat) →
  normalizedCritical balances block positiveScale n ≤ K
criticalScaleBoundImpliesNormalizedBound balances block positiveScale K criticalBound n =
  let
    target = blockTarget block n
    targetPositive = blockTargetPositive block positiveScale n
    reciprocal = positiveReciprocal target targetPositive

    instance
      reciprocalIsNonnegative : NonNegative reciprocal
      reciprocalIsNonnegative =
        ℚ.nonNegative
          (ℚP.<⇒≤
            (let
              instance
                targetIsPositive : Positive target
                targetIsPositive = ℚ.positive targetPositive
                targetIsNonzero : NonZero target
                targetIsNonzero = ℚP.pos⇒nonZero target
                reciprocalIsPositive : Positive (1/ target)
                reciprocalIsPositive = ℚP.1/pos⇒pos target
             in ℚP.positive⁻¹ (1/ target)))

    multiplied :
      criticalValue balances n * reciprocal
      ≤ (K * target) * reciprocal
    multiplied = ℚP.*-monoʳ-≤-nonNeg reciprocal (criticalBound n)

    rhsMeaning : (K * target) * reciprocal ≡ K
    rhsMeaning =
      trans
        (solve (K ∷ target ∷ reciprocal ∷ []))
        (trans
          (cong (K *_) (positiveReciprocalRightInverse target targetPositive))
          (solve (K ∷ [])))
  in
  subst
    (λ right → normalizedCritical balances block positiveScale n ≤ right)
    rhsMeaning
    multiplied

criticalScaleEquivalentToUniformNormalizedBound : Bool
criticalScaleEquivalentToUniformNormalizedBound = true

criticalScaleNormalizationConstructedUpstream : Bool
criticalScaleNormalizationConstructedUpstream = true

criticalScaleEquivalentToUniformNormalizedBoundIsTrue :
  criticalScaleEquivalentToUniformNormalizedBound ≡ true
criticalScaleEquivalentToUniformNormalizedBoundIsTrue = refl

criticalScaleNormalizationConstructedUpstreamIsTrue :
  criticalScaleNormalizationConstructedUpstream ≡ true
criticalScaleNormalizationConstructedUpstreamIsTrue = refl
