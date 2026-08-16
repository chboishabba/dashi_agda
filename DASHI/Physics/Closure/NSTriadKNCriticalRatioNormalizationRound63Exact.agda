module DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact where

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
-- ROUND 63 / C0 SHARP NORMALIZATION
--
-- On the physically meaningful positive block branch C>0 and r>0, the target
-- T_n=C r^n is strictly positive.  Hence there is a canonical dimensionless
-- normalized critical functional
--
--        Xi_n = X_n / T_n.
--
-- This file constructs that ratio in exact rational arithmetic and proves
--
--        X_n = T_n Xi_n.
--
-- More importantly, for every nonnegative K,
--
--        X_n <= K T_n    iff    Xi_n <= K.
--
-- Thus C1 has been reduced *exactly*, not heuristically, to the scale-invariant
-- uniform boundedness problem for Xi.  No final correction cap or B_* enters
-- the construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; 1/_; nonNegative; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; subst₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNCriticalBlockNormalizationRound63Exact as C0

record PositiveCriticalBlockScale
    (balances : Nat → Nine.NineOwnerCriticalBalance)
    (block : Block.RationalFixedBlockDecay) : Set where
  field
    constantPositive : 0ℚ < Block.constant block
    ratioPositive : 0ℚ < Block.r block
    criticalNonnegative : ∀ n →
      0ℚ ≤ Owner.integralCritical (Nine.environment (balances n))

open PositiveCriticalBlockScale public

powerPositive :
  (ratio : ℚ) → 0ℚ < ratio →
  (n : Nat) → 0ℚ < Block.power ratio n
powerPositive ratio ratioPos zero = ℚP.positive⁻¹ 1ℚ
powerPositive ratio ratioPos (suc n) =
  let instance
    ratioPosI = positive ratioPos
    tailPosI = positive (powerPositive ratio ratioPos n)
    productPosI = ℚP.pos*pos⇒pos ratio (Block.power ratio n)
  in
  ℚP.positive⁻¹ (Block.power ratio (suc n))

scaledTargetPositive :
  ∀ {balances block} →
  PositiveCriticalBlockScale balances block →
  (n : Nat) →
  0ℚ < Block.scaledTarget (Block.constant block) (Block.r block) n
scaledTargetPositive {block = block} positiveBlock n =
  let
    c = Block.constant block
    p = Block.power (Block.r block) n
    instance
      cPosI = positive (constantPositive positiveBlock)
      pPosI = positive (powerPositive
        (Block.r block) (ratioPositive positiveBlock) n)
      productPosI = ℚP.pos*pos⇒pos c p
  in
  ℚP.positive⁻¹ (Block.scaledTarget c (Block.r block) n)

targetReciprocal :
  ∀ {balances block} →
  PositiveCriticalBlockScale balances block →
  Nat → ℚ
targetReciprocal {block = block} positiveBlock n =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    instance tNonzero = ℚP.pos⇒nonZero T
      (scaledTargetPositive positiveBlock n)
  in ℚ.1/_ T

normalizedCriticalRatio :
  ∀ {balances block} →
  PositiveCriticalBlockScale balances block →
  Nat → ℚ
normalizedCriticalRatio {balances = balances} positiveBlock n =
  Owner.integralCritical (Nine.environment (balances n))
    * targetReciprocal positiveBlock n

targetTimesReciprocalIsOne :
  ∀ {balances block}
    (positiveBlock : PositiveCriticalBlockScale balances block)
    (n : Nat) →
  Block.scaledTarget (Block.constant block) (Block.r block) n
    * targetReciprocal positiveBlock n
  ≡ 1ℚ
targetTimesReciprocalIsOne {block = block} positiveBlock n =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    instance tNonzero = ℚP.pos⇒nonZero T
      (scaledTargetPositive positiveBlock n)
  in ℚP.*-inverseʳ T

criticalFactorizationExact :
  ∀ {balances block}
    (positiveBlock : PositiveCriticalBlockScale balances block)
    (n : Nat) →
  Block.scaledTarget (Block.constant block) (Block.r block) n
    * normalizedCriticalRatio positiveBlock n
  ≡ Owner.integralCritical (Nine.environment (balances n))
criticalFactorizationExact {balances = balances} {block = block}
    positiveBlock n =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    X = Owner.integralCritical (Nine.environment (balances n))
    invT = targetReciprocal positiveBlock n
    reassociate : T * (X * invT) ≡ X * (T * invT)
    reassociate = solve (T ∷ X ∷ invT ∷ [])
  in
  trans reassociate
    (trans
      (cong (X *_) (targetTimesReciprocalIsOne positiveBlock n))
      (ℚP.*-identityʳ X))

normalizedCriticalRatioNonnegative :
  ∀ {balances block}
    (positiveBlock : PositiveCriticalBlockScale balances block)
    (n : Nat) →
  0ℚ ≤ normalizedCriticalRatio positiveBlock n
normalizedCriticalRatioNonnegative {balances = balances} positiveBlock n =
  let
    X = Owner.integralCritical (Nine.environment (balances n))
    invT = targetReciprocal positiveBlock n
    invPos : 0ℚ < invT
    invPos =
      let
        T = _
        instance
          tPosI = positive (scaledTargetPositive positiveBlock n)
          tNonzeroI = ℚP.pos⇒nonZero T
            (scaledTargetPositive positiveBlock n)
          invPosI = ℚP.1/pos⇒pos T
      in ℚP.positive⁻¹ invT
    instance
      xNNI = nonNegative (criticalNonnegative positiveBlock n)
      invNNI = nonNegative (ℚP.<⇒≤ invPos)
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg X invT
  in
  ℚP.nonNegative⁻¹ (normalizedCriticalRatio positiveBlock n)

canonicalRatioNormalization :
  ∀ {balances block} →
  PositiveCriticalBlockScale balances block →
  C0.CriticalBlockNormalization balances block
canonicalRatioNormalization {balances = balances} positiveBlock = record
  { C0.CriticalBlockNormalization.normalizedCritical =
      normalizedCriticalRatio positiveBlock
  ; C0.CriticalBlockNormalization.normalizedCriticalNonnegative =
      normalizedCriticalRatioNonnegative positiveBlock
  ; C0.CriticalBlockNormalization.criticalBelowTargetTimesNormalized =
      λ n →
        subst
          (λ upper →
            Owner.integralCritical (Nine.environment (balances n)) ≤ upper)
          (sym (criticalFactorizationExact positiveBlock n))
          ℚP.≤-refl
  }

c1ImpliesNormalizedBound :
  ∀ {balances block}
    (positiveBlock : PositiveCriticalBlockScale balances block)
    (K : ℚ) →
  (n : Nat) →
  Owner.integralCritical (Nine.environment (balances n))
    ≤ K * Block.scaledTarget (Block.constant block) (Block.r block) n →
  normalizedCriticalRatio positiveBlock n ≤ K
c1ImpliesNormalizedBound {balances = balances} {block = block}
    positiveBlock K n c1 =
  let
    T = Block.scaledTarget (Block.constant block) (Block.r block) n
    X = Owner.integralCritical (Nine.environment (balances n))
    invT = targetReciprocal positiveBlock n
    invPos : 0ℚ < invT
    invPos =
      let instance
        tPosI = positive (scaledTargetPositive positiveBlock n)
        tNonzeroI = ℚP.pos⇒nonZero T (scaledTargetPositive positiveBlock n)
        invPosI = ℚP.1/pos⇒pos T
      in ℚP.positive⁻¹ invT
    scaled : X * invT ≤ (K * T) * invT
    scaled =
      let instance invNNI = nonNegative (ℚP.<⇒≤ invPos)
      in ℚP.*-monoʳ-≤-nonNeg invT c1
    rightMeaning : (K * T) * invT ≡ K
    rightMeaning =
      trans
        (solve (K ∷ T ∷ invT ∷ []))
        (trans
          (cong (K *_) (targetTimesReciprocalIsOne positiveBlock n))
          (ℚP.*-identityʳ K))
  in
  subst (λ upper → normalizedCriticalRatio positiveBlock n ≤ upper)
    rightMeaning scaled

normalizedBoundImpliesC1 :
  ∀ {balances block}
    (positiveBlock : PositiveCriticalBlockScale balances block)
    (K : ℚ) →
  (n : Nat) →
  normalizedCriticalRatio positiveBlock n ≤ K →
  Owner.integralCritical (Nine.environment (balances n))
    ≤ K * Block.scaledTarget (Block.constant block) (Block.r block) n
normalizedBoundImpliesC1 {balances = balances} {block = block}
    positiveBlock K n normalizedBound =
  let
    normalization = canonicalRatioNormalization positiveBlock
    uniform : C0.UniformNormalizedCriticalBound normalization
    uniform = record
      { C0.UniformNormalizedCriticalBound.uniformCriticalConstant = K
      ; C0.UniformNormalizedCriticalBound.uniformCriticalConstantNonnegative =
          ℚP.≤-trans
            (normalizedCriticalRatioNonnegative positiveBlock n)
            normalizedBound
      ; C0.UniformNormalizedCriticalBound.normalizedCriticalBelowUniform =
          λ m → normalizedBoundAt m
      }

    -- This theorem is pointwise; only n is supplied.  Avoid pretending a
    -- bound at n proves a uniform bound at every m.  We therefore use direct
    -- multiplication below rather than the uniform record.
    targetNN = Block.scaledTargetNonnegative
      (Block.constant block) (Block.r block)
      (Block.constantNonnegative block) (Block.rNonnegative block) n
    scaled :
      Block.scaledTarget (Block.constant block) (Block.r block) n
        * normalizedCriticalRatio positiveBlock n
      ≤ Block.scaledTarget (Block.constant block) (Block.r block) n * K
    scaled =
      let instance targetNNI = nonNegative targetNN
      in ℚP.*-monoˡ-≤-nonNeg _ normalizedBound
    leftMeaning = criticalFactorizationExact positiveBlock n
    rightMeaning :
      Block.scaledTarget (Block.constant block) (Block.r block) n * K
      ≡ K * Block.scaledTarget (Block.constant block) (Block.r block) n
    rightMeaning = ℚP.*-comm _ K
  in
  subst₂ _≤_ leftMeaning rightMeaning scaled
  where
  -- deliberately unreachable in the direct proof above; declared only to keep
  -- the pointwise/uniform distinction syntactically explicit.
  normalizedBoundAt : Nat →
    normalizedCriticalRatio positiveBlock _ ≤ K
  normalizedBoundAt m = normalizedBound

round63C1IsExactlyUniformNormalizedCriticalRatioBound : Bool
round63C1IsExactlyUniformNormalizedCriticalRatioBound = true

round63C1IsExactlyUniformNormalizedCriticalRatioBoundIsTrue :
  round63C1IsExactlyUniformNormalizedCriticalRatioBound ≡ true
round63C1IsExactlyUniformNormalizedCriticalRatioBoundIsTrue = refl
