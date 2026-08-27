{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact where

------------------------------------------------------------------------
-- ROW A: CUBIC COUPLING BUDGET FROM POSITIVE INVERSE-SQUARE DRIFT
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- On the tuned asymptotically-free trajectory write u_j = g_j^{-2}.  A
-- positive beta margin gives u_j-u_{j+1} >= bStar > 0.  This module now owns
-- the complete finite-cutoff implication
--
--   u_j g_j^2 = 1,
--   bStar <= u_j-u_{j+1},
--   0 < g_j <= g_{j+1}
--     ==> (bStar/2) g_j^3 <= g_{j+1}-g_j
--     ==> bStar sum_{j<K} g_j^3 <= 2 (g_K-g_0).
--
-- Thus the cubic history budget is a consequence of the SAME inverse-square
-- beta margin used by Row A, not an additional physical hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; Positive; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)
open import Relation.Nullary.Decidable using (toWitness)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

half halfℚ twoℚ : ℚ
half = + 1 / 2
halfℚ = half
twoℚ = + 2 / 1

cube : ℚ → ℚ
cube g = (g * g) * g

productNonnegative : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
productNonnegative left right leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

mul-nonNeg : ∀ {x y} → 0ℚ ≤ x → 0ℚ ≤ y → 0ℚ ≤ x * y
mul-nonNeg = productNonnegative _ _

scaleˡ-nonNeg : ∀ {c x y} → 0ℚ ≤ c → x ≤ y → c * x ≤ c * y
scaleˡ-nonNeg {c} cNN xy =
  let instance cNonNegative : NonNegative c; cNonNegative = ℚ.nonNegative cNN
  in ℚP.*-monoˡ-≤-nonNeg c xy

scaleʳ-nonNeg : ∀ {c x y} → 0ℚ ≤ c → x ≤ y → x * c ≤ y * c
scaleʳ-nonNeg {c} cNN xy =
  let instance cNonNegative : NonNegative c; cNonNegative = ℚ.nonNegative cNN
  in ℚP.*-monoʳ-≤-nonNeg c xy

transport-≤ : ∀ {x y u v : ℚ} → x ≡ y → u ≡ v → x ≤ u → y ≤ v
transport-≤ refl refl le = le

halfNonnegative : 0ℚ ≤ half
halfNonnegative = ℚP.nonNegative⁻¹ half

halfTimesLowerTimesSumBelowUpperSquare :
  ∀ lower upper →
  0ℚ ≤ lower →
  0ℚ ≤ upper →
  lower ≤ upper →
  half * lower * (lower + upper) ≤ upper * upper
halfTimesLowerTimesSumBelowUpperSquare lower upper lowerNN upperNN lowerBelow =
  let
    lowerSquaredBelowMixed : lower * lower ≤ lower * upper
    lowerSquaredBelowMixed = Norm.scaleNonnegative lower lowerNN lowerBelow

    mixedBelowUpperSquaredRaw : upper * lower ≤ upper * upper
    mixedBelowUpperSquaredRaw = Norm.scaleNonnegative upper upperNN lowerBelow

    mixedBelowUpperSquared : lower * upper ≤ upper * upper
    mixedBelowUpperSquared =
      subst (λ left → left ≤ upper * upper) (ℚP.*-comm upper lower)
        mixedBelowUpperSquaredRaw

    summed :
      (lower * lower) + (lower * upper)
      ≤ (upper * upper) + (upper * upper)
    summed = ℚP.+-mono-≤
      (ℚP.≤-trans lowerSquaredBelowMixed mixedBelowUpperSquared)
      mixedBelowUpperSquared

    scaled = Norm.scaleNonnegative half halfNonnegative summed
  in
  subst
    (λ left → left ≤ upper * upper)
    (ℚRing.solve-∀ lower upper)
    (subst
      (λ right → half * ((lower * lower) + (lower * upper)) ≤ right)
      (ℚRing.solve-∀ upper)
      scaled)

inverseSquareMarginImpliesCubicDrift :
  ∀ bStar lower upper →
  0ℚ ≤ bStar →
  0ℚ ≤ lower →
  0ℚ ≤ upper →
  lower ≤ upper →
  0ℚ < lower + upper →
  bStar * (lower * lower) * (upper * upper)
    ≤ (upper - lower) * (lower + upper) →
  half * bStar * cube lower ≤ upper - lower
inverseSquareMarginImpliesCubicDrift
    bStar lower upper bStarNN lowerNN upperNN lowerBelow sumPositive cross =
  let
    elementary = halfTimesLowerTimesSumBelowUpperSquare
      lower upper lowerNN upperNN lowerBelow

    lowerSquareNN = productNonnegative lower lower lowerNN lowerNN
    scaleNN = productNonnegative bStar (lower * lower) bStarNN lowerSquareNN

    scaled :
      (bStar * (lower * lower)) * (half * lower * (lower + upper))
      ≤ (bStar * (lower * lower)) * (upper * upper)
    scaled = Norm.scaleNonnegative (bStar * (lower * lower)) scaleNN elementary

    throughCross :
      (bStar * (lower * lower)) * (half * lower * (lower + upper))
      ≤ (upper - lower) * (lower + upper)
    throughCross = ℚP.≤-trans
      (subst
        (λ right →
          (bStar * (lower * lower)) * (half * lower * (lower + upper)) ≤ right)
        (ℚRing.solve-∀ bStar lower upper)
        scaled)
      cross

    uncancelled :
      (lower + upper) * (half * bStar * cube lower)
      ≤ (lower + upper) * (upper - lower)
    uncancelled =
      subst
        (λ left → left ≤ (lower + upper) * (upper - lower))
        (ℚRing.solve-∀ bStar lower upper)
        (subst
          (λ right →
            (bStar * (lower * lower)) * (half * lower * (lower + upper)) ≤ right)
          (ℚRing.solve-∀ lower upper)
          throughCross)

    instance
      positiveSum : Positive (lower + upper)
      positiveSum = ℚ.positive sumPositive
  in
  ℚP.*-cancelˡ-≤-pos (lower + upper) uncancelled

-- Clearing the inverse-square relations removes the last hidden premise from
-- the local cubic-drift theorem.
clearedInverseSquareMargin :
  ∀ {m a b} (ua ub : ℚ) →
  0ℚ ≤ a → 0ℚ ≤ b →
  ua * (a * a) ≡ 1ℚ → ub * (b * b) ≡ 1ℚ →
  m ≤ ua - ub →
  m * ((a * a) * (b * b)) ≤ (b - a) * (b + a)
clearedInverseSquareMargin {m} {a} {b} ua ub aNN bNN relA relB margin =
  subst (λ z → m * ((a * a) * (b * b)) ≤ z) evaluate
    (scaleʳ-nonNeg
      (productNonnegative (a * a) (b * b)
        (productNonnegative a a aNN aNN)
        (productNonnegative b b bNN bNN))
      margin)
  where
    expand :
      (ua - ub) * ((a * a) * (b * b))
      ≡ (ua * (a * a)) * (b * b) - (ub * (b * b)) * (a * a)
    expand = ℚRing.solve-∀ ua ub a b

    collapse :
      1ℚ * (b * b) - 1ℚ * (a * a) ≡ (b - a) * (b + a)
    collapse = ℚRing.solve-∀ a b

    evaluate :
      (ua - ub) * ((a * a) * (b * b)) ≡ (b - a) * (b + a)
    evaluate =
      trans expand
        (trans (cong₂ (λ x y → x * (b * b) - y * (a * a)) relA relB) collapse)

-- The finite-indexed physical carrier.  The margin is required only for
-- j < cutoff; requiring a fixed positive decrement forever would eventually
-- contradict u_j = g_j^{-2} > 0.
record InverseSquareMarginFlow (cutoff : Nat) : Set where
  field
    marginConstant : ℚ
    coupling inverseSquare : Nat → ℚ
    couplingPositive : ∀ j → 0ℚ < coupling j
    inverseSquareRelation :
      ∀ j → inverseSquare j * (coupling j * coupling j) ≡ 1ℚ
    couplingMonotone : ∀ j → coupling j ≤ coupling (suc j)
    marginStep :
      ∀ j → j ℕ.< cutoff →
      marginConstant ≤ inverseSquare j - inverseSquare (suc j)

open InverseSquareMarginFlow public

sumCubes : (Nat → ℚ) → Nat → ℚ
sumCubes g zero = 0ℚ
sumCubes g (suc n) = sumCubes g n + cube (g n)

module Flow {cutoff : Nat} (flow : InverseSquareMarginFlow cutoff) where

  marginNonnegative : 0ℚ ≤ marginConstant flow → 0ℚ ≤ marginConstant flow
  marginNonnegative x = x

  stepDrift :
    0ℚ ≤ marginConstant flow →
    ∀ j → j ℕ.< cutoff →
    half * marginConstant flow * cube (coupling flow j)
      ≤ coupling flow (suc j) - coupling flow j
  stepDrift marginNN j j<cutoff =
    inverseSquareMarginImpliesCubicDrift
      (marginConstant flow)
      (coupling flow j)
      (coupling flow (suc j))
      marginNN
      (ℚP.<⇒≤ (couplingPositive flow j))
      (ℚP.<⇒≤ (couplingPositive flow (suc j)))
      (couplingMonotone flow j)
      (ℚP.+-mono-< (couplingPositive flow j)
        (couplingPositive flow (suc j)))
      (clearedInverseSquareMargin
        (inverseSquare flow j)
        (inverseSquare flow (suc j))
        (ℚP.<⇒≤ (couplingPositive flow j))
        (ℚP.<⇒≤ (couplingPositive flow (suc j)))
        (inverseSquareRelation flow j)
        (inverseSquareRelation flow (suc j))
        (marginStep flow j j<cutoff))

  cubicTelescope :
    0ℚ ≤ marginConstant flow →
    ∀ K → K ℕ.≤ cutoff →
    marginConstant flow * sumCubes (coupling flow) K
      ≤ twoℚ * (coupling flow K - coupling flow zero)
  cubicTelescope marginNN zero _ =
    subst (λ right → 0ℚ ≤ right)
      (ℚRing.solve-∀ (coupling flow zero)) ℚP.≤-refl
  cubicTelescope marginNN (suc n) sucN≤ =
    let
      n<cutoff : n ℕ.< cutoff
      n<cutoff = sucN≤

      previous :
        marginConstant flow * sumCubes (coupling flow) n
        ≤ twoℚ * (coupling flow n - coupling flow zero)
      previous = cubicTelescope marginNN n (ℕP.<⇒≤ n<cutoff)

      localHalf = stepDrift marginNN n n<cutoff
      local :
        marginConstant flow * cube (coupling flow n)
        ≤ twoℚ * (coupling flow (suc n) - coupling flow n)
      local =
        let
          doubled = scaleˡ-nonNeg (ℚP.nonNegative⁻¹ twoℚ) localHalf
        in
        subst
          (λ left → left ≤ twoℚ * (coupling flow (suc n) - coupling flow n))
          (ℚRing.solve-∀ (marginConstant flow) (coupling flow n))
          doubled

      added = ℚP.+-mono-≤ previous local
    in
    subst
      (λ left → left ≤ twoℚ * (coupling flow (suc n) - coupling flow zero))
      (ℚRing.solve-∀
        (marginConstant flow)
        (sumCubes (coupling flow) n)
        (coupling flow n))
      (subst
        (λ right →
          marginConstant flow * sumCubes (coupling flow) n
          + marginConstant flow * cube (coupling flow n) ≤ right)
        (ℚRing.solve-∀
          (coupling flow zero) (coupling flow n) (coupling flow (suc n)))
        added)

  cubicSumInTube :
    0ℚ ≤ marginConstant flow →
    ∀ {tubeWidth} →
    (∀ K → coupling flow K - coupling flow zero ≤ tubeWidth) →
    ∀ K → K ℕ.≤ cutoff →
    marginConstant flow * sumCubes (coupling flow) K ≤ twoℚ * tubeWidth
  cubicSumInTube marginNN tube K K≤cutoff =
    ℚP.≤-trans (cubicTelescope marginNN K K≤cutoff)
      (scaleˡ-nonNeg (ℚP.nonNegative⁻¹ twoℚ) (tube K))

-- A concrete one-shell flow used by downstream non-vacuity witnesses.
module PositiveMarginWitness where

  witnessCoupling witnessInverseSquare : Nat → ℚ
  witnessCoupling zero = + 1 / 2
  witnessCoupling (suc _) = 1ℚ
  witnessInverseSquare zero = + 4 / 1
  witnessInverseSquare (suc _) = 1ℚ

  witnessMargin : ℚ
  witnessMargin = + 3 / 1

  witnessFlow : InverseSquareMarginFlow 1
  witnessFlow = record
    { marginConstant = witnessMargin
    ; coupling = witnessCoupling
    ; inverseSquare = witnessInverseSquare
    ; couplingPositive = positive?
    ; inverseSquareRelation = relation
    ; couplingMonotone = monotone
    ; marginStep = margin
    }
    where
      positive? : ∀ j → 0ℚ < witnessCoupling j
      positive? zero = toWitness {a? = 0ℚ ℚP.<? (+ 1 / 2)} _
      positive? (suc _) = toWitness {a? = 0ℚ ℚP.<? 1ℚ} _

      relation :
        ∀ j → witnessInverseSquare j * (witnessCoupling j * witnessCoupling j) ≡ 1ℚ
      relation zero = refl
      relation (suc _) = refl

      monotone : ∀ j → witnessCoupling j ≤ witnessCoupling (suc j)
      monotone zero = toWitness {a? = (+ 1 / 2) ℚP.≤? 1ℚ} _
      monotone (suc _) = ℚP.≤-refl

      margin :
        ∀ j → j ℕ.< 1 →
        witnessMargin ≤ witnessInverseSquare j - witnessInverseSquare (suc j)
      margin zero _ = ℚP.≤-refl
      margin (suc _) (ℕ.s≤s ())
