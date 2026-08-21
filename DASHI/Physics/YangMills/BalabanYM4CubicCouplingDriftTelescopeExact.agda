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
-- MATHEMATICAL ROLE
--
-- On the tuned asymptotically-free trajectory write u_j = g_j^{-2}.  A
-- positive beta margin implies, in the direction from ultraviolet to the
-- prescribed terminal coupling,
--
--       u_j - u_{j+1} >= bStar > 0.
--
-- Cross-multiplication gives
--
--       bStar g_j^2 g_{j+1}^2
--          <= (g_{j+1}-g_j)(g_j+g_{j+1}).
--
-- For 0 <= g_j <= g_{j+1},
--
--       (1/2) g_j (g_j+g_{j+1}) <= g_{j+1}^2,
--
-- and cancellation of the positive sum gives the local cubic drift
--
--       (bStar/2) g_j^3 <= g_{j+1} - g_j.
--
-- Those local inequalities telescope, so the entire marginal history has a
-- cutoff-independent CUBIC budget
--
--       (bStar/2) sum_{j<K} g_j^3 <= g_K - g_0 <= gamma.
--
-- This is the natural shooting-sensitivity budget.  It replaces any false
-- assumption that sum g_j itself is uniformly bounded in K.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; Positive; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

half : ℚ
half = + 1 / 2

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

halfNonnegative : 0ℚ ≤ half
halfNonnegative = ℚP.nonNegative⁻¹ half

-- The elementary inequality which makes inverse-square drift cubic in the
-- coupling.  It is intentionally proved without square roots or division.
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
      subst
        (λ left → left ≤ upper * upper)
        (ℚP.*-comm upper lower)
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
      (λ right →
        half * ((lower * lower) + (lower * upper)) ≤ right)
      (ℚRing.solve-∀ upper)
      scaled)

-- Exact local bridge from the cross-multiplied inverse-square beta margin to
-- cubic coupling drift.  `sumPositive` is automatic on the physical trajectory
-- because the couplings are positive; keeping it explicit avoids importing a
-- separate positivity lemma here.
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
    elementary =
      halfTimesLowerTimesSumBelowUpperSquare
        lower upper lowerNN upperNN lowerBelow

    lowerSquareNN = productNonnegative lower lower lowerNN lowerNN
    scaleNN = productNonnegative bStar (lower * lower) bStarNN lowerSquareNN

    scaled :
      (bStar * (lower * lower))
        * (half * lower * (lower + upper))
      ≤
      (bStar * (lower * lower)) * (upper * upper)
    scaled = Norm.scaleNonnegative
      (bStar * (lower * lower)) scaleNN elementary

    throughCross :
      (bStar * (lower * lower))
        * (half * lower * (lower + upper))
      ≤ (upper - lower) * (lower + upper)
    throughCross =
      ℚP.≤-trans
        (subst
          (λ right →
            (bStar * (lower * lower))
              * (half * lower * (lower + upper)) ≤ right)
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
            (bStar * (lower * lower))
              * (half * lower * (lower + upper)) ≤ right)
          (ℚRing.solve-∀ lower upper)
          throughCross)

    instance
      positiveSum : Positive (lower + upper)
      positiveSum = ℚ.positive sumPositive
  in
  ℚP.*-cancelˡ-≤-pos (lower + upper) uncancelled

data CouplingChain : Set where
  terminal : ℚ → CouplingChain
  _then_ : ℚ → CouplingChain → CouplingChain

first : CouplingChain → ℚ
first (terminal g) = g
first (g then rest) = g

last : CouplingChain → ℚ
last (terminal g) = g
last (_ then rest) = last rest

cubicHistory : CouplingChain → ℚ
cubicHistory (terminal g) = 0ℚ
cubicHistory (g then rest) = cube g + cubicHistory rest

data CubicDrift (bStar : ℚ) : CouplingChain → Set where
  done : ∀ g → CubicDrift bStar (terminal g)
  step : ∀ g {rest} →
    half * bStar * cube g ≤ first rest - g →
    CubicDrift bStar rest →
    CubicDrift bStar (g then rest)

cubicDriftTelescopes :
  ∀ {bStar chain} →
  CubicDrift bStar chain →
  half * bStar * cubicHistory chain ≤ last chain - first chain
cubicDriftTelescopes {bStar = bStar} {chain = terminal g} (done .g) =
  subst
    (λ right → 0ℚ ≤ right)
    (ℚRing.solve-∀ g)
    ℚP.≤-refl
cubicDriftTelescopes {bStar = bStar} {chain = g then rest}
    (step .g local restDrift) =
  let
    tail = cubicDriftTelescopes restDrift
    added = ℚP.+-mono-≤ local tail

    leftExact :
      (half * bStar * cube g)
        + (half * bStar * cubicHistory rest)
      ≡ half * bStar * cubicHistory (g then rest)
    leftExact = ℚRing.solve-∀ bStar g (cubicHistory rest)

    rightExact :
      (first rest - g) + (last rest - first rest)
      ≡ last (g then rest) - first (g then rest)
    rightExact = ℚRing.solve-∀ g (first rest) (last rest)
  in
  subst
    (λ lowerValue → lowerValue ≤ last (g then rest) - first (g then rest))
    leftExact
    (subst
      (λ upperValue →
        (half * bStar * cube g)
          + (half * bStar * cubicHistory rest)
        ≤ upperValue)
      rightExact
      added)

cubicHistoryBelowTerminalWindow :
  ∀ {bStar chain gamma} →
  CubicDrift bStar chain →
  0ℚ ≤ first chain →
  last chain ≤ gamma →
  half * bStar * cubicHistory chain ≤ gamma
cubicHistoryBelowTerminalWindow {chain = chain} drift firstNN terminalBelow =
  let
    telescoped = cubicDriftTelescopes drift

    differenceBelowLast : last chain - first chain ≤ last chain
    differenceBelowLast =
      subst
        (λ left → left ≤ last chain)
        (ℚRing.solve-∀ (last chain) (first chain))
        (ℚP.+-monoʳ-≤
          (last chain)
          (ℚP.neg-mono-≤ firstNN))
  in
  ℚP.≤-trans telescoped
    (ℚP.≤-trans differenceBelowLast terminalBelow)
